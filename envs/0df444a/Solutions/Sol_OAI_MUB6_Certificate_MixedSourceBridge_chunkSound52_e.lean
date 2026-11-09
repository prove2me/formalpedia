-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:59.999446+00:00
-- url     : https://prove2.me/submissions/b2dc54da-e7df-46d9-a8dc-9d80347f371a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3847_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3852_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3853_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3938_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3977_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3982_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3995_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound834_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound840_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound841_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound842_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound844_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound847_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14714 raw14714Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw14714 raw14714Labels = mixedMoment B raw14714step0 raw14714step0Labels := by
      have hz : ∀ j, raw14714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14714step0 = (fun i j => raw14714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14714step0 raw14714; decide +kernel
      have hl : raw14714step0Labels = raw14714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14714 raw14714Labels permutation346 hz
    mixedMoment B raw14714step0 raw14714step0Labels = mixedMoment B raw14714step1 raw14714step1Labels := by
      have ha : raw14714step1 = (fun i j => raw14714step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14714step1 raw14714step0; decide +kernel
      have hl : raw14714step1Labels = raw14714step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14714step0 raw14714step0Labels permutation32 permutation6
    mixedMoment B raw14714step1 raw14714step1Labels = mixedMoment B raw14714step2 raw14714step2Labels := by
      have ha : raw14714step2 = raw14714step1 := by apply Matrix.ext; unfold raw14714step2 raw14714step1; decide +kernel
      have hl : raw14714step1Labels = labelEmbedding9 ∘ raw14714step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14714step1 raw14714step1Labels raw14714step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical14774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14774 raw14774Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw14774 raw14774Labels = mixedMoment B raw14774step0 raw14774step0Labels := by
      have hz : ∀ j, raw14774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14774step0 = (fun i j => raw14774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14774step0 raw14774; decide +kernel
      have hl : raw14774step0Labels = raw14774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14774 raw14774Labels permutation346 hz
    mixedMoment B raw14774step0 raw14774step0Labels = mixedMoment B raw14774step1 raw14774step1Labels := by
      have ha : raw14774step1 = (fun i j => raw14774step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14774step1 raw14774step0; decide +kernel
      have hl : raw14774step1Labels = raw14774step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14774step0 raw14774step0Labels permutation151 permutation7
    mixedMoment B raw14774step1 raw14774step1Labels = mixedMoment B raw14774step2 raw14774step2Labels := by
      have ha : raw14774step2 = -raw14774step1 := by apply Matrix.ext; change ∀ i j, raw14774step2 i j = -(raw14774step1 i j); unfold raw14774step2 raw14774step1; decide +kernel
      have hl : raw14774step2Labels = raw14774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14774step2 raw14774step2Labels = mixedMoment B raw14774step3 raw14774step3Labels := by
      have ha : raw14774step3 = raw14774step2 := by apply Matrix.ext; unfold raw14774step3 raw14774step2; decide +kernel
      have hl : raw14774step2Labels = labelEmbedding1 ∘ raw14774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14774step2 raw14774step2Labels raw14774step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14984 raw14984Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw14984 raw14984Labels = mixedMoment B raw14984step0 raw14984step0Labels := by
      have hz : ∀ j, raw14984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14984step0 = (fun i j => raw14984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14984step0 raw14984; decide +kernel
      have hl : raw14984step0Labels = raw14984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14984 raw14984Labels permutation434 hz
    mixedMoment B raw14984step0 raw14984step0Labels = mixedMoment B raw14984step1 raw14984step1Labels := by
      have ha : raw14984step1 = (fun i j => raw14984step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14984step1 raw14984step0; decide +kernel
      have hl : raw14984step1Labels = raw14984step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14984step0 raw14984step0Labels permutation32 permutation6
    mixedMoment B raw14984step1 raw14984step1Labels = mixedMoment B raw14984step2 raw14984step2Labels := by
      have ha : raw14984step2 = raw14984step1 := by apply Matrix.ext; unfold raw14984step2 raw14984step1; decide +kernel
      have hl : raw14984step1Labels = labelEmbedding9 ∘ raw14984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14984step1 raw14984step1Labels raw14984step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical15006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15006 raw15006Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw15006 raw15006Labels = mixedMoment B raw15006step0 raw15006step0Labels := by
      have hz : ∀ j, raw15006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15006step0 = (fun i j => raw15006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15006step0 raw15006; decide +kernel
      have hl : raw15006step0Labels = raw15006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15006 raw15006Labels permutation434 hz
    mixedMoment B raw15006step0 raw15006step0Labels = mixedMoment B raw15006step1 raw15006step1Labels := by
      have ha : raw15006step1 = (fun i j => raw15006step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15006step1 raw15006step0; decide +kernel
      have hl : raw15006step1Labels = raw15006step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15006step0 raw15006step0Labels permutation151 permutation7
    mixedMoment B raw15006step1 raw15006step1Labels = mixedMoment B raw15006step2 raw15006step2Labels := by
      have ha : raw15006step2 = -raw15006step1 := by apply Matrix.ext; change ∀ i j, raw15006step2 i j = -(raw15006step1 i j); unfold raw15006step2 raw15006step1; decide +kernel
      have hl : raw15006step2Labels = raw15006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15006step2 raw15006step2Labels = mixedMoment B raw15006step3 raw15006step3Labels := by
      have ha : raw15006step3 = raw15006step2 := by apply Matrix.ext; unfold raw15006step3 raw15006step2; decide +kernel
      have hl : raw15006step2Labels = labelEmbedding1 ∘ raw15006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15006step2 raw15006step2Labels raw15006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15117 raw15117Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw15117 raw15117Labels = mixedMoment B raw15117step0 raw15117step0Labels := by
      have hz : ∀ j, raw15117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15117step0 = (fun i j => raw15117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15117step0 raw15117; decide +kernel
      have hl : raw15117step0Labels = raw15117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15117 raw15117Labels permutation346 hz
    mixedMoment B raw15117step0 raw15117step0Labels = mixedMoment B raw15117step1 raw15117step1Labels := by
      have ha : raw15117step1 = (fun i j => raw15117step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15117step1 raw15117step0; decide +kernel
      have hl : raw15117step1Labels = raw15117step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15117step0 raw15117step0Labels permutation151 permutation7
    mixedMoment B raw15117step1 raw15117step1Labels = mixedMoment B raw15117step2 raw15117step2Labels := by
      have ha : raw15117step2 = -raw15117step1 := by apply Matrix.ext; change ∀ i j, raw15117step2 i j = -(raw15117step1 i j); unfold raw15117step2 raw15117step1; decide +kernel
      have hl : raw15117step2Labels = raw15117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15117step2 raw15117step2Labels = mixedMoment B raw15117step3 raw15117step3Labels := by
      have ha : raw15117step3 = raw15117step2 := by apply Matrix.ext; unfold raw15117step3 raw15117step2; decide +kernel
      have hl : raw15117step2Labels = labelEmbedding10 ∘ raw15117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15117step2 raw15117step2Labels raw15117step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical15122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15122 raw15122Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15122 raw15122Labels = mixedMoment B raw15122step0 raw15122step0Labels := by
      have hz : ∀ j, raw15122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15122step0 = (fun i j => raw15122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15122step0 raw15122; decide +kernel
      have hl : raw15122step0Labels = raw15122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15122 raw15122Labels permutation346 hz
    mixedMoment B raw15122step0 raw15122step0Labels = mixedMoment B raw15122step1 raw15122step1Labels := by
      have ha : raw15122step1 = (fun i j => raw15122step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15122step1 raw15122step0; decide +kernel
      have hl : raw15122step1Labels = raw15122step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15122step0 raw15122step0Labels permutation151 permutation7
    mixedMoment B raw15122step1 raw15122step1Labels = mixedMoment B raw15122step2 raw15122step2Labels := by
      have ha : raw15122step2 = -raw15122step1 := by apply Matrix.ext; change ∀ i j, raw15122step2 i j = -(raw15122step1 i j); unfold raw15122step2 raw15122step1; decide +kernel
      have hl : raw15122step2Labels = raw15122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15122step2 raw15122step2Labels = mixedMoment B raw15122step3 raw15122step3Labels := by
      have ha : raw15122step3 = raw15122step2 := by apply Matrix.ext; unfold raw15122step3 raw15122step2; decide +kernel
      have hl : raw15122step2Labels = labelEmbedding10 ∘ raw15122step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15122step2 raw15122step2Labels raw15122step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical15123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15123 raw15123Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw15123 raw15123Labels = mixedMoment B raw15123step0 raw15123step0Labels := by
      have ha : raw15123step0 = (fun i j => raw15123 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15123step0 raw15123; decide +kernel
      have hl : raw15123step0Labels = raw15123Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15123 raw15123Labels permutation164 permutation4
    mixedMoment B raw15123step0 raw15123step0Labels = mixedMoment B raw15123step1 raw15123step1Labels := by
      have ha : raw15123step1 = -raw15123step0 := by apply Matrix.ext; change ∀ i j, raw15123step1 i j = -(raw15123step0 i j); unfold raw15123step1 raw15123step0; decide +kernel
      have hl : raw15123step1Labels = raw15123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15123step1 raw15123step1Labels = mixedMoment B raw15123step2 raw15123step2Labels := by
      have ha : raw15123step2 = raw15123step1 := by apply Matrix.ext; unfold raw15123step2 raw15123step1; decide +kernel
      have hl : raw15123step1Labels = labelEmbedding7 ∘ raw15123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15123step1 raw15123step1Labels raw15123step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

theorem canonical15124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15124 raw15124Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw15124 raw15124Labels = mixedMoment B raw15124step0 raw15124step0Labels := by
      have ha : raw15124step0 = (fun i j => raw15124 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15124step0 raw15124; decide +kernel
      have hl : raw15124step0Labels = raw15124Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15124 raw15124Labels permutation152 permutation6
    mixedMoment B raw15124step0 raw15124step0Labels = mixedMoment B raw15124step1 raw15124step1Labels := by
      have ha : raw15124step1 = raw15124step0 := by apply Matrix.ext; unfold raw15124step1 raw15124step0; decide +kernel
      have hl : raw15124step0Labels = labelEmbedding9 ∘ raw15124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15124step0 raw15124step0Labels raw15124step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical15125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15125 raw15125Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15125 raw15125Labels = mixedMoment B raw15125step0 raw15125step0Labels := by
      have hz : ∀ j, raw15125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15125step0 = (fun i j => raw15125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15125step0 raw15125; decide +kernel
      have hl : raw15125step0Labels = raw15125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15125 raw15125Labels permutation434 hz
    mixedMoment B raw15125step0 raw15125step0Labels = mixedMoment B raw15125step1 raw15125step1Labels := by
      have ha : raw15125step1 = (fun i j => raw15125step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15125step1 raw15125step0; decide +kernel
      have hl : raw15125step1Labels = raw15125step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15125step0 raw15125step0Labels permutation32 permutation6
    mixedMoment B raw15125step1 raw15125step1Labels = mixedMoment B raw15125step2 raw15125step2Labels := by
      have ha : raw15125step2 = raw15125step1 := by apply Matrix.ext; unfold raw15125step2 raw15125step1; decide +kernel
      have hl : raw15125step1Labels = labelEmbedding9 ∘ raw15125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15125step1 raw15125step1Labels raw15125step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical15126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15126 raw15126Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw15126 raw15126Labels = mixedMoment B raw15126step0 raw15126step0Labels := by
      have ha : raw15126step0 = (fun i j => raw15126 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15126step0 raw15126; decide +kernel
      have hl : raw15126step0Labels = raw15126Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15126 raw15126Labels permutation152 permutation6
    mixedMoment B raw15126step0 raw15126step0Labels = mixedMoment B raw15126step1 raw15126step1Labels := by
      have ha : raw15126step1 = raw15126step0 := by apply Matrix.ext; unfold raw15126step1 raw15126step0; decide +kernel
      have hl : raw15126step0Labels = labelEmbedding9 ∘ raw15126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15126step0 raw15126step0Labels raw15126step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical15132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15132 raw15132Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15132 raw15132Labels = mixedMoment B raw15132step0 raw15132step0Labels := by
      have hz : ∀ j, raw15132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15132step0 = (fun i j => raw15132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15132step0 raw15132; decide +kernel
      have hl : raw15132step0Labels = raw15132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15132 raw15132Labels permutation346 hz
    mixedMoment B raw15132step0 raw15132step0Labels = mixedMoment B raw15132step1 raw15132step1Labels := by
      have ha : raw15132step1 = (fun i j => raw15132step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15132step1 raw15132step0; decide +kernel
      have hl : raw15132step1Labels = raw15132step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15132step0 raw15132step0Labels permutation146 permutation2
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical15144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15144 raw15144Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw15144 raw15144Labels = mixedMoment B raw15144step0 raw15144step0Labels := by
      have hz : ∀ j, raw15144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15144step0 = (fun i j => raw15144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15144step0 raw15144; decide +kernel
      have hl : raw15144step0Labels = raw15144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15144 raw15144Labels permutation346 hz
    mixedMoment B raw15144step0 raw15144step0Labels = mixedMoment B raw15144step1 raw15144step1Labels := by
      have ha : raw15144step1 = (fun i j => raw15144step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15144step1 raw15144step0; decide +kernel
      have hl : raw15144step1Labels = raw15144step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15144step0 raw15144step0Labels permutation151 permutation7
    mixedMoment B raw15144step1 raw15144step1Labels = mixedMoment B raw15144step2 raw15144step2Labels := by
      have ha : raw15144step2 = -raw15144step1 := by apply Matrix.ext; change ∀ i j, raw15144step2 i j = -(raw15144step1 i j); unfold raw15144step2 raw15144step1; decide +kernel
      have hl : raw15144step2Labels = raw15144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15144step2 raw15144step2Labels = mixedMoment B raw15144step3 raw15144step3Labels := by
      have ha : raw15144step3 = raw15144step2 := by apply Matrix.ext; unfold raw15144step3 raw15144step2; decide +kernel
      have hl : raw15144step2Labels = labelEmbedding1 ∘ raw15144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15144step2 raw15144step2Labels raw15144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical15149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15149 raw15149Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw15149 raw15149Labels = mixedMoment B raw15149step0 raw15149step0Labels := by
      have hz : ∀ j, raw15149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15149step0 = (fun i j => raw15149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15149step0 raw15149; decide +kernel
      have hl : raw15149step0Labels = raw15149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15149 raw15149Labels permutation346 hz
    mixedMoment B raw15149step0 raw15149step0Labels = mixedMoment B raw15149step1 raw15149step1Labels := by
      have ha : raw15149step1 = (fun i j => raw15149step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15149step1 raw15149step0; decide +kernel
      have hl : raw15149step1Labels = raw15149step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15149step0 raw15149step0Labels permutation151 permutation7
    mixedMoment B raw15149step1 raw15149step1Labels = mixedMoment B raw15149step2 raw15149step2Labels := by
      have ha : raw15149step2 = -raw15149step1 := by apply Matrix.ext; change ∀ i j, raw15149step2 i j = -(raw15149step1 i j); unfold raw15149step2 raw15149step1; decide +kernel
      have hl : raw15149step2Labels = raw15149step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15149step2 raw15149step2Labels = mixedMoment B raw15149step3 raw15149step3Labels := by
      have ha : raw15149step3 = raw15149step2 := by apply Matrix.ext; unfold raw15149step3 raw15149step2; decide +kernel
      have hl : raw15149step2Labels = labelEmbedding1 ∘ raw15149step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15149step2 raw15149step2Labels raw15149step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical15150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15150 raw15150Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw15150 raw15150Labels = mixedMoment B raw15150step0 raw15150step0Labels := by
      have ha : raw15150step0 = (fun i j => raw15150 (permutation228 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15150step0 raw15150; decide +kernel
      have hl : raw15150step0Labels = raw15150Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15150 raw15150Labels permutation228 permutation5
    mixedMoment B raw15150step0 raw15150step0Labels = mixedMoment B raw15150step1 raw15150step1Labels := by
      have ha : raw15150step1 = -raw15150step0 := by apply Matrix.ext; change ∀ i j, raw15150step1 i j = -(raw15150step0 i j); unfold raw15150step1 raw15150step0; decide +kernel
      have hl : raw15150step1Labels = raw15150step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15150step1 raw15150step1Labels = mixedMoment B raw15150step2 raw15150step2Labels := by
      have ha : raw15150step2 = raw15150step1 := by apply Matrix.ext; unfold raw15150step2 raw15150step1; decide +kernel
      have hl : raw15150step1Labels = labelEmbedding1 ∘ raw15150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15150step1 raw15150step1Labels raw15150step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3085 node3085Labels := by rfl

theorem canonical15151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15151 raw15151Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw15151 raw15151Labels = mixedMoment B raw15151step0 raw15151step0Labels := by
      have ha : raw15151step0 = (fun i j => raw15151 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15151step0 raw15151; decide +kernel
      have hl : raw15151step0Labels = raw15151Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15151 raw15151Labels permutation682 permutation7
    mixedMoment B raw15151step0 raw15151step0Labels = mixedMoment B raw15151step1 raw15151step1Labels := by
      have ha : raw15151step1 = -raw15151step0 := by apply Matrix.ext; change ∀ i j, raw15151step1 i j = -(raw15151step0 i j); unfold raw15151step1 raw15151step0; decide +kernel
      have hl : raw15151step1Labels = raw15151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15151step1 raw15151step1Labels = mixedMoment B raw15151step2 raw15151step2Labels := by
      have ha : raw15151step2 = raw15151step1 := by apply Matrix.ext; unfold raw15151step2 raw15151step1; decide +kernel
      have hl : raw15151step1Labels = labelEmbedding1 ∘ raw15151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15151step1 raw15151step1Labels raw15151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

theorem canonical15152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15152 raw15152Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw15152 raw15152Labels = mixedMoment B raw15152step0 raw15152step0Labels := by
      have hz : ∀ j, raw15152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15152step0 = (fun i j => raw15152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15152step0 raw15152; decide +kernel
      have hl : raw15152step0Labels = raw15152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15152 raw15152Labels permutation434 hz
    mixedMoment B raw15152step0 raw15152step0Labels = mixedMoment B raw15152step1 raw15152step1Labels := by
      have ha : raw15152step1 = (fun i j => raw15152step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15152step1 raw15152step0; decide +kernel
      have hl : raw15152step1Labels = raw15152step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15152step0 raw15152step0Labels permutation151 permutation7
    mixedMoment B raw15152step1 raw15152step1Labels = mixedMoment B raw15152step2 raw15152step2Labels := by
      have ha : raw15152step2 = -raw15152step1 := by apply Matrix.ext; change ∀ i j, raw15152step2 i j = -(raw15152step1 i j); unfold raw15152step2 raw15152step1; decide +kernel
      have hl : raw15152step2Labels = raw15152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15152step2 raw15152step2Labels = mixedMoment B raw15152step3 raw15152step3Labels := by
      have ha : raw15152step3 = raw15152step2 := by apply Matrix.ext; unfold raw15152step3 raw15152step2; decide +kernel
      have hl : raw15152step2Labels = labelEmbedding1 ∘ raw15152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15152step2 raw15152step2Labels raw15152step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3982 node3982Labels := by rfl

theorem canonical15153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15153 raw15153Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15153 raw15153Labels = mixedMoment B raw15153step0 raw15153step0Labels := by
      have ha : raw15153step0 = (fun i j => raw15153 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15153step0 raw15153; decide +kernel
      have hl : raw15153step0Labels = raw15153Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15153 raw15153Labels permutation682 permutation7
    mixedMoment B raw15153step0 raw15153step0Labels = mixedMoment B raw15153step1 raw15153step1Labels := by
      have ha : raw15153step1 = -raw15153step0 := by apply Matrix.ext; change ∀ i j, raw15153step1 i j = -(raw15153step0 i j); unfold raw15153step1 raw15153step0; decide +kernel
      have hl : raw15153step1Labels = raw15153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15153step1 raw15153step1Labels = mixedMoment B raw15153step2 raw15153step2Labels := by
      have ha : raw15153step2 = raw15153step1 := by apply Matrix.ext; unfold raw15153step2 raw15153step1; decide +kernel
      have hl : raw15153step1Labels = labelEmbedding1 ∘ raw15153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15153step1 raw15153step1Labels raw15153step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical15159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15159 raw15159Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw15159 raw15159Labels = mixedMoment B raw15159step0 raw15159step0Labels := by
      have hz : ∀ j, raw15159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15159step0 = (fun i j => raw15159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15159step0 raw15159; decide +kernel
      have hl : raw15159step0Labels = raw15159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15159 raw15159Labels permutation346 hz
    mixedMoment B raw15159step0 raw15159step0Labels = mixedMoment B raw15159step1 raw15159step1Labels := by
      have ha : raw15159step1 = (fun i j => raw15159step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15159step1 raw15159step0; decide +kernel
      have hl : raw15159step1Labels = raw15159step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15159step0 raw15159step0Labels permutation151 permutation7
    mixedMoment B raw15159step1 raw15159step1Labels = mixedMoment B raw15159step2 raw15159step2Labels := by
      have ha : raw15159step2 = -raw15159step1 := by apply Matrix.ext; change ∀ i j, raw15159step2 i j = -(raw15159step1 i j); unfold raw15159step2 raw15159step1; decide +kernel
      have hl : raw15159step2Labels = raw15159step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15159step2 raw15159step2Labels = mixedMoment B raw15159step3 raw15159step3Labels := by
      have ha : raw15159step3 = raw15159step2 := by apply Matrix.ext; unfold raw15159step3 raw15159step2; decide +kernel
      have hl : raw15159step2Labels = labelEmbedding1 ∘ raw15159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15159step2 raw15159step2Labels raw15159step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical15204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15204 raw15204Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw15204 raw15204Labels = mixedMoment B raw15204step0 raw15204step0Labels := by
      have ha : raw15204step0 = (fun i j => raw15204 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15204step0 raw15204; decide +kernel
      have hl : raw15204step0Labels = raw15204Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15204 raw15204Labels permutation170 permutation4
    mixedMoment B raw15204step0 raw15204step0Labels = mixedMoment B raw15204step1 raw15204step1Labels := by
      have ha : raw15204step1 = -raw15204step0 := by apply Matrix.ext; change ∀ i j, raw15204step1 i j = -(raw15204step0 i j); unfold raw15204step1 raw15204step0; decide +kernel
      have hl : raw15204step1Labels = raw15204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15204step1 raw15204step1Labels = mixedMoment B raw15204step2 raw15204step2Labels := by
      have ha : raw15204step2 = raw15204step1 := by apply Matrix.ext; unfold raw15204step2 raw15204step1; decide +kernel
      have hl : raw15204step1Labels = labelEmbedding7 ∘ raw15204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15204step1 raw15204step1Labels raw15204step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical15205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15205 raw15205Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw15205 raw15205Labels = mixedMoment B raw15205step0 raw15205step0Labels := by
      have ha : raw15205step0 = (fun i j => raw15205 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15205step0 raw15205; decide +kernel
      have hl : raw15205step0Labels = raw15205Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15205 raw15205Labels permutation152 permutation6
    mixedMoment B raw15205step0 raw15205step0Labels = mixedMoment B raw15205step1 raw15205step1Labels := by
      have ha : raw15205step1 = raw15205step0 := by apply Matrix.ext; unfold raw15205step1 raw15205step0; decide +kernel
      have hl : raw15205step0Labels = labelEmbedding9 ∘ raw15205step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15205step0 raw15205step0Labels raw15205step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical15206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15206 raw15206Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw15206 raw15206Labels = mixedMoment B raw15206step0 raw15206step0Labels := by
      have ha : raw15206step0 = (fun i j => raw15206 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15206step0 raw15206; decide +kernel
      have hl : raw15206step0Labels = raw15206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15206 raw15206Labels permutation668 permutation2
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical15210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15210 raw15210Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15210 raw15210Labels = mixedMoment B raw15210step0 raw15210step0Labels := by
      have hz : ∀ j, raw15210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15210step0 = (fun i j => raw15210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15210step0 raw15210; decide +kernel
      have hl : raw15210step0Labels = raw15210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15210 raw15210Labels permutation346 hz
    mixedMoment B raw15210step0 raw15210step0Labels = mixedMoment B raw15210step1 raw15210step1Labels := by
      have ha : raw15210step1 = (fun i j => raw15210step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15210step1 raw15210step0; decide +kernel
      have hl : raw15210step1Labels = raw15210step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15210step0 raw15210step0Labels permutation32 permutation6
    mixedMoment B raw15210step1 raw15210step1Labels = mixedMoment B raw15210step2 raw15210step2Labels := by
      have ha : raw15210step2 = raw15210step1 := by apply Matrix.ext; unfold raw15210step2 raw15210step1; decide +kernel
      have hl : raw15210step1Labels = labelEmbedding9 ∘ raw15210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15210step1 raw15210step1Labels raw15210step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15633 raw15633Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15633 raw15633Labels = mixedMoment B raw15633step0 raw15633step0Labels := by
      have ha : raw15633step0 = (fun i j => raw15633 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15633step0 raw15633; decide +kernel
      have hl : raw15633step0Labels = raw15633Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15633 raw15633Labels permutation682 permutation2
    mixedMoment B raw15633step0 raw15633step0Labels = mixedMoment B raw15633step1 raw15633step1Labels := by
      have ha : raw15633step1 = -raw15633step0 := by apply Matrix.ext; change ∀ i j, raw15633step1 i j = -(raw15633step0 i j); unfold raw15633step1 raw15633step0; decide +kernel
      have hl : raw15633step1Labels = raw15633step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical15639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15639 raw15639Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw15639 raw15639Labels = mixedMoment B raw15639step0 raw15639step0Labels := by
      have hz : ∀ j, raw15639 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw15639step0 = (fun i j => raw15639 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw15639step0 raw15639; decide +kernel
      have hl : raw15639step0Labels = raw15639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15639 raw15639Labels permutation152 hz
    mixedMoment B raw15639step0 raw15639step0Labels = mixedMoment B raw15639step1 raw15639step1Labels := by
      have ha : raw15639step1 = (fun i j => raw15639step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw15639step1 raw15639step0; decide +kernel
      have hl : raw15639step1Labels = raw15639step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15639step0 raw15639step0Labels permutation122 permutation0
    mixedMoment B raw15639step1 raw15639step1Labels = mixedMoment B raw15639step2 raw15639step2Labels := by
      have ha : raw15639step2 = -raw15639step1 := by apply Matrix.ext; change ∀ i j, raw15639step2 i j = -(raw15639step1 i j); unfold raw15639step2 raw15639step1; decide +kernel
      have hl : raw15639step2Labels = raw15639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical15644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15644 raw15644Labels = mixedMoment B node2858 node2858Labels := by
  calc
    mixedMoment B raw15644 raw15644Labels = mixedMoment B raw15644step0 raw15644step0Labels := by
      have ha : raw15644step0 = (fun i j => raw15644 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15644step0 raw15644; decide +kernel
      have hl : raw15644step0Labels = raw15644Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15644 raw15644Labels permutation682 permutation2
    mixedMoment B raw15644step0 raw15644step0Labels = mixedMoment B raw15644step1 raw15644step1Labels := by
      have ha : raw15644step1 = -raw15644step0 := by apply Matrix.ext; change ∀ i j, raw15644step1 i j = -(raw15644step0 i j); unfold raw15644step1 raw15644step0; decide +kernel
      have hl : raw15644step1Labels = raw15644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2858 node2858Labels := by rfl

theorem canonical15652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15652 raw15652Labels = mixedMoment B node2859 node2859Labels := by
  calc
    mixedMoment B raw15652 raw15652Labels = mixedMoment B raw15652step0 raw15652step0Labels := by
      have ha : raw15652step0 = (fun i j => raw15652 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15652step0 raw15652; decide +kernel
      have hl : raw15652step0Labels = raw15652Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15652 raw15652Labels permutation681 permutation2
    mixedMoment B raw15652step0 raw15652step0Labels = mixedMoment B raw15652step1 raw15652step1Labels := by
      have ha : raw15652step1 = -raw15652step0 := by apply Matrix.ext; change ∀ i j, raw15652step1 i j = -(raw15652step0 i j); unfold raw15652step1 raw15652step0; decide +kernel
      have hl : raw15652step1Labels = raw15652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2859 node2859Labels := by rfl

theorem canonical15658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15658 raw15658Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw15658 raw15658Labels = mixedMoment B raw15658step0 raw15658step0Labels := by
      have ha : raw15658step0 = (fun i j => raw15658 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15658step0 raw15658; decide +kernel
      have hl : raw15658step0Labels = raw15658Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15658 raw15658Labels permutation686 permutation2
    mixedMoment B raw15658step0 raw15658step0Labels = mixedMoment B raw15658step1 raw15658step1Labels := by
      have ha : raw15658step1 = -raw15658step0 := by apply Matrix.ext; change ∀ i j, raw15658step1 i j = -(raw15658step0 i j); unfold raw15658step1 raw15658step0; decide +kernel
      have hl : raw15658step1Labels = raw15658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2864 node2864Labels := by rfl

theorem canonical15662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15662 raw15662Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw15662 raw15662Labels = mixedMoment B raw15662step0 raw15662step0Labels := by
      have ha : raw15662step0 = (fun i j => raw15662 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15662step0 raw15662; decide +kernel
      have hl : raw15662step0Labels = raw15662Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15662 raw15662Labels permutation682 permutation2
    mixedMoment B raw15662step0 raw15662step0Labels = mixedMoment B raw15662step1 raw15662step1Labels := by
      have ha : raw15662step1 = -raw15662step0 := by apply Matrix.ext; change ∀ i j, raw15662step1 i j = -(raw15662step0 i j); unfold raw15662step1 raw15662step0; decide +kernel
      have hl : raw15662step1Labels = raw15662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3030 node3030Labels := by rfl

theorem canonical15663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15663 raw15663Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw15663 raw15663Labels = mixedMoment B raw15663step0 raw15663step0Labels := by
      have ha : raw15663step0 = (fun i j => raw15663 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15663step0 raw15663; decide +kernel
      have hl : raw15663step0Labels = raw15663Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15663 raw15663Labels permutation680 permutation2
    mixedMoment B raw15663step0 raw15663step0Labels = mixedMoment B raw15663step1 raw15663step1Labels := by
      have ha : raw15663step1 = -raw15663step0 := by apply Matrix.ext; change ∀ i j, raw15663step1 i j = -(raw15663step0 i j); unfold raw15663step1 raw15663step0; decide +kernel
      have hl : raw15663step1Labels = raw15663step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2864 node2864Labels := by rfl

theorem canonical15667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15667 raw15667Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw15667 raw15667Labels = mixedMoment B raw15667step0 raw15667step0Labels := by
      have ha : raw15667step0 = (fun i j => raw15667 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15667step0 raw15667; decide +kernel
      have hl : raw15667step0Labels = raw15667Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15667 raw15667Labels permutation682 permutation2
    _ = mixedMoment B node5365 node5365Labels := by rfl

theorem canonical15671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15671 raw15671Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw15671 raw15671Labels = mixedMoment B raw15671step0 raw15671step0Labels := by
      have ha : raw15671step0 = (fun i j => raw15671 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15671step0 raw15671; decide +kernel
      have hl : raw15671step0Labels = raw15671Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15671 raw15671Labels permutation668 permutation2
    _ = mixedMoment B node5359 node5359Labels := by rfl

theorem canonical15676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15676 raw15676Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw15676 raw15676Labels = mixedMoment B raw15676step0 raw15676step0Labels := by
      have ha : raw15676step0 = (fun i j => raw15676 (permutation669 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15676step0 raw15676; decide +kernel
      have hl : raw15676step0Labels = raw15676Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15676 raw15676Labels permutation669 permutation2
    _ = mixedMoment B node5360 node5360Labels := by rfl

theorem canonical15680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15680 raw15680Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw15680 raw15680Labels = mixedMoment B raw15680step0 raw15680step0Labels := by
      have ha : raw15680step0 = (fun i j => raw15680 (permutation667 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15680step0 raw15680; decide +kernel
      have hl : raw15680step0Labels = raw15680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15680 raw15680Labels permutation667 permutation2
    _ = mixedMoment B node5360 node5360Labels := by rfl

theorem canonical15685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15685 raw15685Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw15685 raw15685Labels = mixedMoment B raw15685step0 raw15685step0Labels := by
      have ha : raw15685step0 = (fun i j => raw15685 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15685step0 raw15685; decide +kernel
      have hl : raw15685step0Labels = raw15685Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15685 raw15685Labels permutation152 permutation6
    _ = mixedMoment B node3976 node3976Labels := by rfl

theorem canonical15686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15686 raw15686Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw15686 raw15686Labels = mixedMoment B raw15686step0 raw15686step0Labels := by
      have hz : ∀ j, raw15686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15686step0 = (fun i j => raw15686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15686step0 raw15686; decide +kernel
      have hl : raw15686step0Labels = raw15686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15686 raw15686Labels permutation346 hz
    mixedMoment B raw15686step0 raw15686step0Labels = mixedMoment B raw15686step1 raw15686step1Labels := by
      have ha : raw15686step1 = (fun i j => raw15686step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15686step1 raw15686step0; decide +kernel
      have hl : raw15686step1Labels = raw15686step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15686step0 raw15686step0Labels permutation32 permutation6
    _ = mixedMoment B node3995 node3995Labels := by rfl

theorem canonical15687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15687 raw15687Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw15687 raw15687Labels = mixedMoment B raw15687step0 raw15687step0Labels := by
      have hz : ∀ j, raw15687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15687step0 = (fun i j => raw15687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15687step0 raw15687; decide +kernel
      have hl : raw15687step0Labels = raw15687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15687 raw15687Labels permutation434 hz
    mixedMoment B raw15687step0 raw15687step0Labels = mixedMoment B raw15687step1 raw15687step1Labels := by
      have ha : raw15687step1 = (fun i j => raw15687step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15687step1 raw15687step0; decide +kernel
      have hl : raw15687step1Labels = raw15687step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15687step0 raw15687step0Labels permutation32 permutation6
    _ = mixedMoment B node3995 node3995Labels := by rfl

theorem canonical15688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15688 raw15688Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw15688 raw15688Labels = mixedMoment B raw15688step0 raw15688step0Labels := by
      have ha : raw15688step0 = (fun i j => raw15688 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15688step0 raw15688; decide +kernel
      have hl : raw15688step0Labels = raw15688Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15688 raw15688Labels permutation569 permutation3
    _ = mixedMoment B node2631 node2631Labels := by rfl

theorem canonical15689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15689 raw15689Labels = mixedMoment B node3938 node3938Labels := by
  calc
    mixedMoment B raw15689 raw15689Labels = mixedMoment B raw15689step0 raw15689step0Labels := by
      have ha : raw15689step0 = (fun i j => raw15689 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15689step0 raw15689; decide +kernel
      have hl : raw15689step0Labels = raw15689Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15689 raw15689Labels permutation569 permutation3
    _ = mixedMoment B node3938 node3938Labels := by rfl

theorem canonical15690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15690 raw15690Labels = mixedMoment B node3566 node3566Labels := by
  calc
    mixedMoment B raw15690 raw15690Labels = mixedMoment B raw15690step0 raw15690step0Labels := by
      have ha : raw15690step0 = (fun i j => raw15690 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15690step0 raw15690; decide +kernel
      have hl : raw15690step0Labels = raw15690Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15690 raw15690Labels permutation152 permutation6
    _ = mixedMoment B node3566 node3566Labels := by rfl

theorem canonical15691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15691 raw15691Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw15691 raw15691Labels = mixedMoment B raw15691step0 raw15691step0Labels := by
      have hz : ∀ j, raw15691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15691step0 = (fun i j => raw15691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15691step0 raw15691; decide +kernel
      have hl : raw15691step0Labels = raw15691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15691 raw15691Labels permutation346 hz
    mixedMoment B raw15691step0 raw15691step0Labels = mixedMoment B raw15691step1 raw15691step1Labels := by
      have ha : raw15691step1 = (fun i j => raw15691step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15691step1 raw15691step0; decide +kernel
      have hl : raw15691step1Labels = raw15691step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15691step0 raw15691step0Labels permutation32 permutation6
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical15692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15692 raw15692Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw15692 raw15692Labels = mixedMoment B raw15692step0 raw15692step0Labels := by
      have hz : ∀ j, raw15692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15692step0 = (fun i j => raw15692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15692step0 raw15692; decide +kernel
      have hl : raw15692step0Labels = raw15692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15692 raw15692Labels permutation434 hz
    mixedMoment B raw15692step0 raw15692step0Labels = mixedMoment B raw15692step1 raw15692step1Labels := by
      have ha : raw15692step1 = (fun i j => raw15692step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15692step1 raw15692step0; decide +kernel
      have hl : raw15692step1Labels = raw15692step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15692step0 raw15692step0Labels permutation32 permutation6
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical15693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15693 raw15693Labels = mixedMoment B node2607 node2607Labels := by
  calc
    mixedMoment B raw15693 raw15693Labels = mixedMoment B raw15693step0 raw15693step0Labels := by
      have ha : raw15693step0 = (fun i j => raw15693 (permutation572 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15693step0 raw15693; decide +kernel
      have hl : raw15693step0Labels = raw15693Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15693 raw15693Labels permutation572 permutation3
    _ = mixedMoment B node2607 node2607Labels := by rfl

theorem canonical15694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15694 raw15694Labels = mixedMoment B node3878 node3878Labels := by
  calc
    mixedMoment B raw15694 raw15694Labels = mixedMoment B raw15694step0 raw15694step0Labels := by
      have ha : raw15694step0 = (fun i j => raw15694 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15694step0 raw15694; decide +kernel
      have hl : raw15694step0Labels = raw15694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15694 raw15694Labels permutation152 permutation6
    _ = mixedMoment B node3878 node3878Labels := by rfl

theorem canonical15695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15695 raw15695Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw15695 raw15695Labels = mixedMoment B raw15695step0 raw15695step0Labels := by
      have ha : raw15695step0 = (fun i j => raw15695 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15695step0 raw15695; decide +kernel
      have hl : raw15695step0Labels = raw15695Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15695 raw15695Labels permutation158 permutation6
    _ = mixedMoment B node3527 node3527Labels := by rfl

theorem canonical15696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15696 raw15696Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw15696 raw15696Labels = mixedMoment B raw15696step0 raw15696step0Labels := by
      have ha : raw15696step0 = (fun i j => raw15696 (permutation386 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15696step0 raw15696; decide +kernel
      have hl : raw15696step0Labels = raw15696Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15696 raw15696Labels permutation386 permutation3
    mixedMoment B raw15696step0 raw15696step0Labels = mixedMoment B raw15696step1 raw15696step1Labels := by
      have ha : raw15696step1 = -raw15696step0 := by apply Matrix.ext; change ∀ i j, raw15696step1 i j = -(raw15696step0 i j); unfold raw15696step1 raw15696step0; decide +kernel
      have hl : raw15696step1Labels = raw15696step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3802 node3802Labels := by rfl

theorem canonical15697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15697 raw15697Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw15697 raw15697Labels = mixedMoment B raw15697step0 raw15697step0Labels := by
      have hz : ∀ j, raw15697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15697step0 = (fun i j => raw15697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15697step0 raw15697; decide +kernel
      have hl : raw15697step0Labels = raw15697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15697 raw15697Labels permutation434 hz
    mixedMoment B raw15697step0 raw15697step0Labels = mixedMoment B raw15697step1 raw15697step1Labels := by
      have ha : raw15697step1 = (fun i j => raw15697step0 (permutation87 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15697step1 raw15697step0; decide +kernel
      have hl : raw15697step1Labels = raw15697step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15697step0 raw15697step0Labels permutation87 permutation3
    mixedMoment B raw15697step1 raw15697step1Labels = mixedMoment B raw15697step2 raw15697step2Labels := by
      have ha : raw15697step2 = -raw15697step1 := by apply Matrix.ext; change ∀ i j, raw15697step2 i j = -(raw15697step1 i j); unfold raw15697step2 raw15697step1; decide +kernel
      have hl : raw15697step2Labels = raw15697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical15698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15698 raw15698Labels = mixedMoment B node2606 node2606Labels := by
  calc
    mixedMoment B raw15698 raw15698Labels = mixedMoment B raw15698step0 raw15698step0Labels := by
      have ha : raw15698step0 = (fun i j => raw15698 (permutation570 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15698step0 raw15698; decide +kernel
      have hl : raw15698step0Labels = raw15698Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15698 raw15698Labels permutation570 permutation3
    _ = mixedMoment B node2606 node2606Labels := by rfl

theorem canonical15699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15699 raw15699Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw15699 raw15699Labels = mixedMoment B raw15699step0 raw15699step0Labels := by
      have ha : raw15699step0 = (fun i j => raw15699 (permutation386 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15699step0 raw15699; decide +kernel
      have hl : raw15699step0Labels = raw15699Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15699 raw15699Labels permutation386 permutation3
    mixedMoment B raw15699step0 raw15699step0Labels = mixedMoment B raw15699step1 raw15699step1Labels := by
      have ha : raw15699step1 = -raw15699step0 := by apply Matrix.ext; change ∀ i j, raw15699step1 i j = -(raw15699step0 i j); unfold raw15699step1 raw15699step0; decide +kernel
      have hl : raw15699step1Labels = raw15699step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3780 node3780Labels := by rfl

theorem canonical15700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15700 raw15700Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw15700 raw15700Labels = mixedMoment B raw15700step0 raw15700step0Labels := by
      have ha : raw15700step0 = (fun i j => raw15700 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15700step0 raw15700; decide +kernel
      have hl : raw15700step0Labels = raw15700Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15700 raw15700Labels permutation152 permutation6
    _ = mixedMoment B node3527 node3527Labels := by rfl

theorem canonical15701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15701 raw15701Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw15701 raw15701Labels = mixedMoment B raw15701step0 raw15701step0Labels := by
      have ha : raw15701step0 = (fun i j => raw15701 (permutation471 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15701step0 raw15701; decide +kernel
      have hl : raw15701step0Labels = raw15701Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15701 raw15701Labels permutation471 permutation3
    mixedMoment B raw15701step0 raw15701step0Labels = mixedMoment B raw15701step1 raw15701step1Labels := by
      have ha : raw15701step1 = -raw15701step0 := by apply Matrix.ext; change ∀ i j, raw15701step1 i j = -(raw15701step0 i j); unfold raw15701step1 raw15701step0; decide +kernel
      have hl : raw15701step1Labels = raw15701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3802 node3802Labels := by rfl

theorem canonical15702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15702 raw15702Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw15702 raw15702Labels = mixedMoment B raw15702step0 raw15702step0Labels := by
      have hz : ∀ j, raw15702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15702step0 = (fun i j => raw15702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15702step0 raw15702; decide +kernel
      have hl : raw15702step0Labels = raw15702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15702 raw15702Labels permutation346 hz
    mixedMoment B raw15702step0 raw15702step0Labels = mixedMoment B raw15702step1 raw15702step1Labels := by
      have ha : raw15702step1 = (fun i j => raw15702step0 (permutation87 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15702step1 raw15702step0; decide +kernel
      have hl : raw15702step1Labels = raw15702step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15702step0 raw15702step0Labels permutation87 permutation3
    mixedMoment B raw15702step1 raw15702step1Labels = mixedMoment B raw15702step2 raw15702step2Labels := by
      have ha : raw15702step2 = -raw15702step1 := by apply Matrix.ext; change ∀ i j, raw15702step2 i j = -(raw15702step1 i j); unfold raw15702step2 raw15702step1; decide +kernel
      have hl : raw15702step2Labels = raw15702step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical15703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15703 raw15703Labels = mixedMoment B node2606 node2606Labels := by
  calc
    mixedMoment B raw15703 raw15703Labels = mixedMoment B raw15703step0 raw15703step0Labels := by
      have ha : raw15703step0 = (fun i j => raw15703 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15703step0 raw15703; decide +kernel
      have hl : raw15703step0Labels = raw15703Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15703 raw15703Labels permutation569 permutation3
    _ = mixedMoment B node2606 node2606Labels := by rfl

theorem canonical15704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15704 raw15704Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw15704 raw15704Labels = mixedMoment B raw15704step0 raw15704step0Labels := by
      have ha : raw15704step0 = (fun i j => raw15704 (permutation471 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15704step0 raw15704; decide +kernel
      have hl : raw15704step0Labels = raw15704Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15704 raw15704Labels permutation471 permutation3
    mixedMoment B raw15704step0 raw15704step0Labels = mixedMoment B raw15704step1 raw15704step1Labels := by
      have ha : raw15704step1 = -raw15704step0 := by apply Matrix.ext; change ∀ i j, raw15704step1 i j = -(raw15704step0 i j); unfold raw15704step1 raw15704step0; decide +kernel
      have hl : raw15704step1Labels = raw15704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3780 node3780Labels := by rfl

theorem canonical15705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15705 raw15705Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw15705 raw15705Labels = mixedMoment B raw15705step0 raw15705step0Labels := by
      have ha : raw15705step0 = (fun i j => raw15705 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15705step0 raw15705; decide +kernel
      have hl : raw15705step0Labels = raw15705Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15705 raw15705Labels permutation152 permutation6
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical15706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15706 raw15706Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw15706 raw15706Labels = mixedMoment B raw15706step0 raw15706step0Labels := by
      have ha : raw15706step0 = (fun i j => raw15706 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15706step0 raw15706; decide +kernel
      have hl : raw15706step0Labels = raw15706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15706 raw15706Labels permutation152 permutation6
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical15707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15707 raw15707Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw15707 raw15707Labels = mixedMoment B raw15707step0 raw15707step0Labels := by
      have hz : ∀ j, raw15707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15707step0 = (fun i j => raw15707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15707step0 raw15707; decide +kernel
      have hl : raw15707step0Labels = raw15707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15707 raw15707Labels permutation346 hz
    mixedMoment B raw15707step0 raw15707step0Labels = mixedMoment B raw15707step1 raw15707step1Labels := by
      have ha : raw15707step1 = (fun i j => raw15707step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15707step1 raw15707step0; decide +kernel
      have hl : raw15707step1Labels = raw15707step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15707step0 raw15707step0Labels permutation32 permutation6
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical15708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15708 raw15708Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw15708 raw15708Labels = mixedMoment B raw15708step0 raw15708step0Labels := by
      have hz : ∀ j, raw15708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15708step0 = (fun i j => raw15708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15708step0 raw15708; decide +kernel
      have hl : raw15708step0Labels = raw15708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15708 raw15708Labels permutation434 hz
    mixedMoment B raw15708step0 raw15708step0Labels = mixedMoment B raw15708step1 raw15708step1Labels := by
      have ha : raw15708step1 = (fun i j => raw15708step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15708step1 raw15708step0; decide +kernel
      have hl : raw15708step1Labels = raw15708step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15708step0 raw15708step0Labels permutation32 permutation6
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical15709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15709 raw15709Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw15709 raw15709Labels = mixedMoment B raw15709step0 raw15709step0Labels := by
      have ha : raw15709step0 = (fun i j => raw15709 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15709step0 raw15709; decide +kernel
      have hl : raw15709step0Labels = raw15709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15709 raw15709Labels permutation152 permutation6
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical15710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15710 raw15710Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw15710 raw15710Labels = mixedMoment B raw15710step0 raw15710step0Labels := by
      have ha : raw15710step0 = (fun i j => raw15710 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15710step0 raw15710; decide +kernel
      have hl : raw15710step0Labels = raw15710Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15710 raw15710Labels permutation152 permutation6
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical15711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15711 raw15711Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw15711 raw15711Labels = mixedMoment B raw15711step0 raw15711step0Labels := by
      have ha : raw15711step0 = (fun i j => raw15711 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15711step0 raw15711; decide +kernel
      have hl : raw15711step0Labels = raw15711Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15711 raw15711Labels permutation152 permutation6
    _ = mixedMoment B node3799 node3799Labels := by rfl

theorem canonical15712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15712 raw15712Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15712 raw15712Labels = mixedMoment B raw15712step0 raw15712step0Labels := by
      have hz : ∀ j, raw15712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15712step0 = (fun i j => raw15712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15712step0 raw15712; decide +kernel
      have hl : raw15712step0Labels = raw15712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15712 raw15712Labels permutation346 hz
    mixedMoment B raw15712step0 raw15712step0Labels = mixedMoment B raw15712step1 raw15712step1Labels := by
      have ha : raw15712step1 = (fun i j => raw15712step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15712step1 raw15712step0; decide +kernel
      have hl : raw15712step1Labels = raw15712step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15712step0 raw15712step0Labels permutation32 permutation6
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical15713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15713 raw15713Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15713 raw15713Labels = mixedMoment B raw15713step0 raw15713step0Labels := by
      have hz : ∀ j, raw15713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15713step0 = (fun i j => raw15713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15713step0 raw15713; decide +kernel
      have hl : raw15713step0Labels = raw15713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15713 raw15713Labels permutation434 hz
    mixedMoment B raw15713step0 raw15713step0Labels = mixedMoment B raw15713step1 raw15713step1Labels := by
      have ha : raw15713step1 = (fun i j => raw15713step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15713step1 raw15713step0; decide +kernel
      have hl : raw15713step1Labels = raw15713step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15713step0 raw15713step0Labels permutation32 permutation6
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical15714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15714 raw15714Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw15714 raw15714Labels = mixedMoment B raw15714step0 raw15714step0Labels := by
      have ha : raw15714step0 = (fun i j => raw15714 (permutation526 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15714step0 raw15714; decide +kernel
      have hl : raw15714step0Labels = raw15714Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15714 raw15714Labels permutation526 permutation3
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical15718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15718 raw15718Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw15718 raw15718Labels = mixedMoment B raw15718step0 raw15718step0Labels := by
      have ha : raw15718step0 = (fun i j => raw15718 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15718step0 raw15718; decide +kernel
      have hl : raw15718step0Labels = raw15718Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15718 raw15718Labels permutation682 permutation7
    mixedMoment B raw15718step0 raw15718step0Labels = mixedMoment B raw15718step1 raw15718step1Labels := by
      have ha : raw15718step1 = -raw15718step0 := by apply Matrix.ext; change ∀ i j, raw15718step1 i j = -(raw15718step0 i j); unfold raw15718step1 raw15718step0; decide +kernel
      have hl : raw15718step1Labels = raw15718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15718step1 raw15718step1Labels = mixedMoment B raw15718step2 raw15718step2Labels := by
      have ha : raw15718step2 = raw15718step1 := by apply Matrix.ext; unfold raw15718step2 raw15718step1; decide +kernel
      have hl : raw15718step1Labels = labelEmbedding1 ∘ raw15718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15718step1 raw15718step1Labels raw15718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

theorem canonical15722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15722 raw15722Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw15722 raw15722Labels = mixedMoment B raw15722step0 raw15722step0Labels := by
      have ha : raw15722step0 = (fun i j => raw15722 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15722step0 raw15722; decide +kernel
      have hl : raw15722step0Labels = raw15722Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15722 raw15722Labels permutation682 permutation7
    mixedMoment B raw15722step0 raw15722step0Labels = mixedMoment B raw15722step1 raw15722step1Labels := by
      have ha : raw15722step1 = -raw15722step0 := by apply Matrix.ext; change ∀ i j, raw15722step1 i j = -(raw15722step0 i j); unfold raw15722step1 raw15722step0; decide +kernel
      have hl : raw15722step1Labels = raw15722step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15722step1 raw15722step1Labels = mixedMoment B raw15722step2 raw15722step2Labels := by
      have ha : raw15722step2 = raw15722step1 := by apply Matrix.ext; unfold raw15722step2 raw15722step1; decide +kernel
      have hl : raw15722step1Labels = labelEmbedding1 ∘ raw15722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15722step1 raw15722step1Labels raw15722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

theorem canonical15727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15727 raw15727Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw15727 raw15727Labels = mixedMoment B raw15727step0 raw15727step0Labels := by
      have ha : raw15727step0 = (fun i j => raw15727 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15727step0 raw15727; decide +kernel
      have hl : raw15727step0Labels = raw15727Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15727 raw15727Labels permutation688 permutation7
    mixedMoment B raw15727step0 raw15727step0Labels = mixedMoment B raw15727step1 raw15727step1Labels := by
      have ha : raw15727step1 = -raw15727step0 := by apply Matrix.ext; change ∀ i j, raw15727step1 i j = -(raw15727step0 i j); unfold raw15727step1 raw15727step0; decide +kernel
      have hl : raw15727step1Labels = raw15727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15727step1 raw15727step1Labels = mixedMoment B raw15727step2 raw15727step2Labels := by
      have ha : raw15727step2 = raw15727step1 := by apply Matrix.ext; unfold raw15727step2 raw15727step1; decide +kernel
      have hl : raw15727step1Labels = labelEmbedding1 ∘ raw15727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15727step1 raw15727step1Labels raw15727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

theorem canonical15731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15731 raw15731Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw15731 raw15731Labels = mixedMoment B raw15731step0 raw15731step0Labels := by
      have ha : raw15731step0 = (fun i j => raw15731 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15731step0 raw15731; decide +kernel
      have hl : raw15731step0Labels = raw15731Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15731 raw15731Labels permutation682 permutation7
    mixedMoment B raw15731step0 raw15731step0Labels = mixedMoment B raw15731step1 raw15731step1Labels := by
      have ha : raw15731step1 = -raw15731step0 := by apply Matrix.ext; change ∀ i j, raw15731step1 i j = -(raw15731step0 i j); unfold raw15731step1 raw15731step0; decide +kernel
      have hl : raw15731step1Labels = raw15731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15731step1 raw15731step1Labels = mixedMoment B raw15731step2 raw15731step2Labels := by
      have ha : raw15731step2 = raw15731step1 := by apply Matrix.ext; unfold raw15731step2 raw15731step1; decide +kernel
      have hl : raw15731step1Labels = labelEmbedding1 ∘ raw15731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15731step1 raw15731step1Labels raw15731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

theorem canonical15732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15732 raw15732Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw15732 raw15732Labels = mixedMoment B raw15732step0 raw15732step0Labels := by
      have hz : ∀ j, raw15732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15732step0 = (fun i j => raw15732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15732step0 raw15732; decide +kernel
      have hl : raw15732step0Labels = raw15732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15732 raw15732Labels permutation346 hz
    mixedMoment B raw15732step0 raw15732step0Labels = mixedMoment B raw15732step1 raw15732step1Labels := by
      have ha : raw15732step1 = (fun i j => raw15732step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15732step1 raw15732step0; decide +kernel
      have hl : raw15732step1Labels = raw15732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15732step0 raw15732step0Labels permutation151 permutation7
    mixedMoment B raw15732step1 raw15732step1Labels = mixedMoment B raw15732step2 raw15732step2Labels := by
      have ha : raw15732step2 = -raw15732step1 := by apply Matrix.ext; change ∀ i j, raw15732step2 i j = -(raw15732step1 i j); unfold raw15732step2 raw15732step1; decide +kernel
      have hl : raw15732step2Labels = raw15732step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15732step2 raw15732step2Labels = mixedMoment B raw15732step3 raw15732step3Labels := by
      have ha : raw15732step3 = raw15732step2 := by apply Matrix.ext; unfold raw15732step3 raw15732step2; decide +kernel
      have hl : raw15732step2Labels = labelEmbedding1 ∘ raw15732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15732step2 raw15732step2Labels raw15732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3982 node3982Labels := by rfl

theorem canonical15737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15737 raw15737Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw15737 raw15737Labels = mixedMoment B raw15737step0 raw15737step0Labels := by
      have ha : raw15737step0 = (fun i j => raw15737 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15737step0 raw15737; decide +kernel
      have hl : raw15737step0Labels = raw15737Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15737 raw15737Labels permutation224 permutation4
    mixedMoment B raw15737step0 raw15737step0Labels = mixedMoment B raw15737step1 raw15737step1Labels := by
      have ha : raw15737step1 = -raw15737step0 := by apply Matrix.ext; change ∀ i j, raw15737step1 i j = -(raw15737step0 i j); unfold raw15737step1 raw15737step0; decide +kernel
      have hl : raw15737step1Labels = raw15737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical15738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15738 raw15738Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw15738 raw15738Labels = mixedMoment B raw15738step0 raw15738step0Labels := by
      have ha : raw15738step0 = (fun i j => raw15738 (permutation577 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15738step0 raw15738; decide +kernel
      have hl : raw15738step0Labels = raw15738Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15738 raw15738Labels permutation577 permutation2
    _ = mixedMoment B node3956 node3956Labels := by rfl

theorem canonical15739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15739 raw15739Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw15739 raw15739Labels = mixedMoment B raw15739step0 raw15739step0Labels := by
      have hz : ∀ j, raw15739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15739step0 = (fun i j => raw15739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15739step0 raw15739; decide +kernel
      have hl : raw15739step0Labels = raw15739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15739 raw15739Labels permutation346 hz
    mixedMoment B raw15739step0 raw15739step0Labels = mixedMoment B raw15739step1 raw15739step1Labels := by
      have ha : raw15739step1 = (fun i j => raw15739step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15739step1 raw15739step0; decide +kernel
      have hl : raw15739step1Labels = raw15739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15739step0 raw15739step0Labels permutation127 permutation2
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical15740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15740 raw15740Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw15740 raw15740Labels = mixedMoment B raw15740step0 raw15740step0Labels := by
      have hz : ∀ j, raw15740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15740step0 = (fun i j => raw15740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15740step0 raw15740; decide +kernel
      have hl : raw15740step0Labels = raw15740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15740 raw15740Labels permutation434 hz
    mixedMoment B raw15740step0 raw15740step0Labels = mixedMoment B raw15740step1 raw15740step1Labels := by
      have ha : raw15740step1 = (fun i j => raw15740step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15740step1 raw15740step0; decide +kernel
      have hl : raw15740step1Labels = raw15740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15740step0 raw15740step0Labels permutation127 permutation2
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical15741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15741 raw15741Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw15741 raw15741Labels = mixedMoment B raw15741step0 raw15741step0Labels := by
      have ha : raw15741step0 = (fun i j => raw15741 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15741step0 raw15741; decide +kernel
      have hl : raw15741step0Labels = raw15741Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15741 raw15741Labels permutation584 permutation2
    _ = mixedMoment B node2878 node2878Labels := by rfl

theorem canonical15742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15742 raw15742Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw15742 raw15742Labels = mixedMoment B raw15742step0 raw15742step0Labels := by
      have ha : raw15742step0 = (fun i j => raw15742 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15742step0 raw15742; decide +kernel
      have hl : raw15742step0Labels = raw15742Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15742 raw15742Labels permutation682 permutation2
    _ = mixedMoment B node3703 node3703Labels := by rfl

theorem canonical15743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15743 raw15743Labels = mixedMoment B node2630 node2630Labels := by
  calc
    mixedMoment B raw15743 raw15743Labels = mixedMoment B raw15743step0 raw15743step0Labels := by
      have ha : raw15743step0 = (fun i j => raw15743 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15743step0 raw15743; decide +kernel
      have hl : raw15743step0Labels = raw15743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15743 raw15743Labels permutation224 permutation4
    mixedMoment B raw15743step0 raw15743step0Labels = mixedMoment B raw15743step1 raw15743step1Labels := by
      have ha : raw15743step1 = -raw15743step0 := by apply Matrix.ext; change ∀ i j, raw15743step1 i j = -(raw15743step0 i j); unfold raw15743step1 raw15743step0; decide +kernel
      have hl : raw15743step1Labels = raw15743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2630 node2630Labels := by rfl

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

theorem canonical15745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15745 raw15745Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15745 raw15745Labels = mixedMoment B raw15745step0 raw15745step0Labels := by
      have hz : ∀ j, raw15745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15745step0 = (fun i j => raw15745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15745step0 raw15745; decide +kernel
      have hl : raw15745step0Labels = raw15745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15745 raw15745Labels permutation434 hz
    mixedMoment B raw15745step0 raw15745step0Labels = mixedMoment B raw15745step1 raw15745step1Labels := by
      have ha : raw15745step1 = (fun i j => raw15745step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15745step1 raw15745step0; decide +kernel
      have hl : raw15745step1Labels = raw15745step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15745step0 raw15745step0Labels permutation44 permutation4
    mixedMoment B raw15745step1 raw15745step1Labels = mixedMoment B raw15745step2 raw15745step2Labels := by
      have ha : raw15745step2 = -raw15745step1 := by apply Matrix.ext; change ∀ i j, raw15745step2 i j = -(raw15745step1 i j); unfold raw15745step2 raw15745step1; decide +kernel
      have hl : raw15745step2Labels = raw15745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical15746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15746 raw15746Labels = mixedMoment B node2869 node2869Labels := by
  calc
    mixedMoment B raw15746 raw15746Labels = mixedMoment B raw15746step0 raw15746step0Labels := by
      have ha : raw15746step0 = (fun i j => raw15746 (permutation572 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15746step0 raw15746; decide +kernel
      have hl : raw15746step0Labels = raw15746Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15746 raw15746Labels permutation572 permutation2
    _ = mixedMoment B node2869 node2869Labels := by rfl

theorem canonical15747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15747 raw15747Labels = mixedMoment B node3697 node3697Labels := by
  calc
    mixedMoment B raw15747 raw15747Labels = mixedMoment B raw15747step0 raw15747step0Labels := by
      have ha : raw15747step0 = (fun i j => raw15747 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15747step0 raw15747; decide +kernel
      have hl : raw15747step0Labels = raw15747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15747 raw15747Labels permutation668 permutation2
    _ = mixedMoment B node3697 node3697Labels := by rfl

theorem canonical15748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15748 raw15748Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw15748 raw15748Labels = mixedMoment B raw15748step0 raw15748step0Labels := by
      have ha : raw15748step0 = (fun i j => raw15748 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15748step0 raw15748; decide +kernel
      have hl : raw15748step0Labels = raw15748Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15748 raw15748Labels permutation167 permutation4
    mixedMoment B raw15748step0 raw15748step0Labels = mixedMoment B raw15748step1 raw15748step1Labels := by
      have ha : raw15748step1 = -raw15748step0 := by apply Matrix.ext; change ∀ i j, raw15748step1 i j = -(raw15748step0 i j); unfold raw15748step1 raw15748step0; decide +kernel
      have hl : raw15748step1Labels = raw15748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3788 node3788Labels := by rfl

theorem canonical15749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15749 raw15749Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw15749 raw15749Labels = mixedMoment B raw15749step0 raw15749step0Labels := by
      have ha : raw15749step0 = (fun i j => raw15749 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15749step0 raw15749; decide +kernel
      have hl : raw15749step0Labels = raw15749Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15749 raw15749Labels permutation165 permutation4
    mixedMoment B raw15749step0 raw15749step0Labels = mixedMoment B raw15749step1 raw15749step1Labels := by
      have ha : raw15749step1 = -raw15749step0 := by apply Matrix.ext; change ∀ i j, raw15749step1 i j = -(raw15749step0 i j); unfold raw15749step1 raw15749step0; decide +kernel
      have hl : raw15749step1Labels = raw15749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3788 node3788Labels := by rfl

theorem canonical15750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15750 raw15750Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw15750 raw15750Labels = mixedMoment B raw15750step0 raw15750step0Labels := by
      have ha : raw15750step0 = (fun i j => raw15750 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15750step0 raw15750; decide +kernel
      have hl : raw15750step0Labels = raw15750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15750 raw15750Labels permutation164 permutation4
    mixedMoment B raw15750step0 raw15750step0Labels = mixedMoment B raw15750step1 raw15750step1Labels := by
      have ha : raw15750step1 = -raw15750step0 := by apply Matrix.ext; change ∀ i j, raw15750step1 i j = -(raw15750step0 i j); unfold raw15750step1 raw15750step0; decide +kernel
      have hl : raw15750step1Labels = raw15750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3805 node3805Labels := by rfl

theorem canonical15751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15751 raw15751Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw15751 raw15751Labels = mixedMoment B raw15751step0 raw15751step0Labels := by
      have ha : raw15751step0 = (fun i j => raw15751 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15751step0 raw15751; decide +kernel
      have hl : raw15751step0Labels = raw15751Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15751 raw15751Labels permutation164 permutation4
    mixedMoment B raw15751step0 raw15751step0Labels = mixedMoment B raw15751step1 raw15751step1Labels := by
      have ha : raw15751step1 = -raw15751step0 := by apply Matrix.ext; change ∀ i j, raw15751step1 i j = -(raw15751step0 i j); unfold raw15751step1 raw15751step0; decide +kernel
      have hl : raw15751step1Labels = raw15751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3786 node3786Labels := by rfl

theorem canonical15752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15752 raw15752Labels = mixedMoment B node2870 node2870Labels := by
  calc
    mixedMoment B raw15752 raw15752Labels = mixedMoment B raw15752step0 raw15752step0Labels := by
      have ha : raw15752step0 = (fun i j => raw15752 (permutation573 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15752step0 raw15752; decide +kernel
      have hl : raw15752step0Labels = raw15752Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15752 raw15752Labels permutation573 permutation2
    _ = mixedMoment B node2870 node2870Labels := by rfl

theorem canonical15753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15753 raw15753Labels = mixedMoment B node2870 node2870Labels := by
  calc
    mixedMoment B raw15753 raw15753Labels = mixedMoment B raw15753step0 raw15753step0Labels := by
      have ha : raw15753step0 = (fun i j => raw15753 (permutation571 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15753step0 raw15753; decide +kernel
      have hl : raw15753step0Labels = raw15753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15753 raw15753Labels permutation571 permutation2
    _ = mixedMoment B node2870 node2870Labels := by rfl

theorem canonical15754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15754 raw15754Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw15754 raw15754Labels = mixedMoment B raw15754step0 raw15754step0Labels := by
      have ha : raw15754step0 = (fun i j => raw15754 (permutation572 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15754step0 raw15754; decide +kernel
      have hl : raw15754step0Labels = raw15754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15754 raw15754Labels permutation572 permutation2
    _ = mixedMoment B node3043 node3043Labels := by rfl

theorem canonical15755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15755 raw15755Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw15755 raw15755Labels = mixedMoment B raw15755step0 raw15755step0Labels := by
      have ha : raw15755step0 = (fun i j => raw15755 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15755step0 raw15755; decide +kernel
      have hl : raw15755step0Labels = raw15755Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15755 raw15755Labels permutation224 permutation4
    mixedMoment B raw15755step0 raw15755step0Labels = mixedMoment B raw15755step1 raw15755step1Labels := by
      have ha : raw15755step1 = -raw15755step0 := by apply Matrix.ext; change ∀ i j, raw15755step1 i j = -(raw15755step0 i j); unfold raw15755step1 raw15755step0; decide +kernel
      have hl : raw15755step1Labels = raw15755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2614 node2614Labels := by rfl

theorem canonical15756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15756 raw15756Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15756 raw15756Labels = mixedMoment B raw15756step0 raw15756step0Labels := by
      have hz : ∀ j, raw15756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15756step0 = (fun i j => raw15756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15756step0 raw15756; decide +kernel
      have hl : raw15756step0Labels = raw15756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15756 raw15756Labels permutation346 hz
    mixedMoment B raw15756step0 raw15756step0Labels = mixedMoment B raw15756step1 raw15756step1Labels := by
      have ha : raw15756step1 = (fun i j => raw15756step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15756step1 raw15756step0; decide +kernel
      have hl : raw15756step1Labels = raw15756step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15756step0 raw15756step0Labels permutation143 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical15757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15757 raw15757Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15757 raw15757Labels = mixedMoment B raw15757step0 raw15757step0Labels := by
      have hz : ∀ j, raw15757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15757step0 = (fun i j => raw15757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15757step0 raw15757; decide +kernel
      have hl : raw15757step0Labels = raw15757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15757 raw15757Labels permutation434 hz
    mixedMoment B raw15757step0 raw15757step0Labels = mixedMoment B raw15757step1 raw15757step1Labels := by
      have ha : raw15757step1 = (fun i j => raw15757step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15757step1 raw15757step0; decide +kernel
      have hl : raw15757step1Labels = raw15757step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15757step0 raw15757step0Labels permutation143 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical15858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15858 raw15858Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw15858 raw15858Labels = mixedMoment B raw15858step0 raw15858step0Labels := by
      have ha : raw15858step0 = (fun i j => raw15858 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15858step0 raw15858; decide +kernel
      have hl : raw15858step0Labels = raw15858Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15858 raw15858Labels permutation682 permutation7
    mixedMoment B raw15858step0 raw15858step0Labels = mixedMoment B raw15858step1 raw15858step1Labels := by
      have ha : raw15858step1 = -raw15858step0 := by apply Matrix.ext; change ∀ i j, raw15858step1 i j = -(raw15858step0 i j); unfold raw15858step1 raw15858step0; decide +kernel
      have hl : raw15858step1Labels = raw15858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15858step1 raw15858step1Labels = mixedMoment B raw15858step2 raw15858step2Labels := by
      have ha : raw15858step2 = raw15858step1 := by apply Matrix.ext; unfold raw15858step2 raw15858step1; decide +kernel
      have hl : raw15858step1Labels = labelEmbedding10 ∘ raw15858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15858step1 raw15858step1Labels raw15858step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical15859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15859 raw15859Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw15859 raw15859Labels = mixedMoment B raw15859step0 raw15859step0Labels := by
      have hz : ∀ j, raw15859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15859step0 = (fun i j => raw15859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15859step0 raw15859; decide +kernel
      have hl : raw15859step0Labels = raw15859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15859 raw15859Labels permutation434 hz
    mixedMoment B raw15859step0 raw15859step0Labels = mixedMoment B raw15859step1 raw15859step1Labels := by
      have ha : raw15859step1 = (fun i j => raw15859step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15859step1 raw15859step0; decide +kernel
      have hl : raw15859step1Labels = raw15859step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15859step0 raw15859step0Labels permutation151 permutation7
    mixedMoment B raw15859step1 raw15859step1Labels = mixedMoment B raw15859step2 raw15859step2Labels := by
      have ha : raw15859step2 = -raw15859step1 := by apply Matrix.ext; change ∀ i j, raw15859step2 i j = -(raw15859step1 i j); unfold raw15859step2 raw15859step1; decide +kernel
      have hl : raw15859step2Labels = raw15859step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15859step2 raw15859step2Labels = mixedMoment B raw15859step3 raw15859step3Labels := by
      have ha : raw15859step3 = raw15859step2 := by apply Matrix.ext; unfold raw15859step3 raw15859step2; decide +kernel
      have hl : raw15859step2Labels = labelEmbedding10 ∘ raw15859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15859step2 raw15859step2Labels raw15859step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical15860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15860 raw15860Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw15860 raw15860Labels = mixedMoment B raw15860step0 raw15860step0Labels := by
      have ha : raw15860step0 = (fun i j => raw15860 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15860step0 raw15860; decide +kernel
      have hl : raw15860step0Labels = raw15860Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15860 raw15860Labels permutation682 permutation2
    _ = mixedMoment B node5098 node5098Labels := by rfl

theorem canonical15861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15861 raw15861Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw15861 raw15861Labels = mixedMoment B raw15861step0 raw15861step0Labels := by
      have ha : raw15861step0 = (fun i j => raw15861 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15861step0 raw15861; decide +kernel
      have hl : raw15861step0Labels = raw15861Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15861 raw15861Labels permutation240 permutation4
    mixedMoment B raw15861step0 raw15861step0Labels = mixedMoment B raw15861step1 raw15861step1Labels := by
      have ha : raw15861step1 = -raw15861step0 := by apply Matrix.ext; change ∀ i j, raw15861step1 i j = -(raw15861step0 i j); unfold raw15861step1 raw15861step0; decide +kernel
      have hl : raw15861step1Labels = raw15861step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15861step1 raw15861step1Labels = mixedMoment B raw15861step2 raw15861step2Labels := by
      have ha : raw15861step2 = raw15861step1 := by apply Matrix.ext; unfold raw15861step2 raw15861step1; decide +kernel
      have hl : raw15861step1Labels = labelEmbedding7 ∘ raw15861step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15861step1 raw15861step1Labels raw15861step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical15862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15862 raw15862Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15862 raw15862Labels = mixedMoment B raw15862step0 raw15862step0Labels := by
      have hz : ∀ j, raw15862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15862step0 = (fun i j => raw15862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15862step0 raw15862; decide +kernel
      have hl : raw15862step0Labels = raw15862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15862 raw15862Labels permutation434 hz
    mixedMoment B raw15862step0 raw15862step0Labels = mixedMoment B raw15862step1 raw15862step1Labels := by
      have ha : raw15862step1 = (fun i j => raw15862step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15862step1 raw15862step0; decide +kernel
      have hl : raw15862step1Labels = raw15862step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15862step0 raw15862step0Labels permutation151 permutation7
    mixedMoment B raw15862step1 raw15862step1Labels = mixedMoment B raw15862step2 raw15862step2Labels := by
      have ha : raw15862step2 = -raw15862step1 := by apply Matrix.ext; change ∀ i j, raw15862step2 i j = -(raw15862step1 i j); unfold raw15862step2 raw15862step1; decide +kernel
      have hl : raw15862step2Labels = raw15862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15862step2 raw15862step2Labels = mixedMoment B raw15862step3 raw15862step3Labels := by
      have ha : raw15862step3 = raw15862step2 := by apply Matrix.ext; unfold raw15862step3 raw15862step2; decide +kernel
      have hl : raw15862step2Labels = labelEmbedding10 ∘ raw15862step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15862step2 raw15862step2Labels raw15862step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical15863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15863 raw15863Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw15863 raw15863Labels = mixedMoment B raw15863step0 raw15863step0Labels := by
      have ha : raw15863step0 = (fun i j => raw15863 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15863step0 raw15863; decide +kernel
      have hl : raw15863step0Labels = raw15863Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15863 raw15863Labels permutation668 permutation2
    _ = mixedMoment B node5085 node5085Labels := by rfl

theorem canonical15864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15864 raw15864Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw15864 raw15864Labels = mixedMoment B raw15864step0 raw15864step0Labels := by
      have ha : raw15864step0 = (fun i j => raw15864 (permutation169 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15864step0 raw15864; decide +kernel
      have hl : raw15864step0Labels = raw15864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15864 raw15864Labels permutation169 permutation4
    mixedMoment B raw15864step0 raw15864step0Labels = mixedMoment B raw15864step1 raw15864step1Labels := by
      have ha : raw15864step1 = -raw15864step0 := by apply Matrix.ext; change ∀ i j, raw15864step1 i j = -(raw15864step0 i j); unfold raw15864step1 raw15864step0; decide +kernel
      have hl : raw15864step1Labels = raw15864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15864step1 raw15864step1Labels = mixedMoment B raw15864step2 raw15864step2Labels := by
      have ha : raw15864step2 = raw15864step1 := by apply Matrix.ext; unfold raw15864step2 raw15864step1; decide +kernel
      have hl : raw15864step1Labels = labelEmbedding7 ∘ raw15864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15864step1 raw15864step1Labels raw15864step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

theorem canonical15865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15865 raw15865Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw15865 raw15865Labels = mixedMoment B raw15865step0 raw15865step0Labels := by
      have ha : raw15865step0 = (fun i j => raw15865 (permutation672 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15865step0 raw15865; decide +kernel
      have hl : raw15865step0Labels = raw15865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15865 raw15865Labels permutation672 permutation2
    _ = mixedMoment B node5407 node5407Labels := by rfl

theorem canonical15866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15866 raw15866Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15866 raw15866Labels = mixedMoment B raw15866step0 raw15866step0Labels := by
      have hz : ∀ j, raw15866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15866step0 = (fun i j => raw15866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15866step0 raw15866; decide +kernel
      have hl : raw15866step0Labels = raw15866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15866 raw15866Labels permutation434 hz
    mixedMoment B raw15866step0 raw15866step0Labels = mixedMoment B raw15866step1 raw15866step1Labels := by
      have ha : raw15866step1 = (fun i j => raw15866step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15866step1 raw15866step0; decide +kernel
      have hl : raw15866step1Labels = raw15866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15866step0 raw15866step0Labels permutation146 permutation2
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical15867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15867 raw15867Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw15867 raw15867Labels = mixedMoment B raw15867step0 raw15867step0Labels := by
      have ha : raw15867step0 = (fun i j => raw15867 (permutation669 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15867step0 raw15867; decide +kernel
      have hl : raw15867step0Labels = raw15867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15867 raw15867Labels permutation669 permutation2
    _ = mixedMoment B node5086 node5086Labels := by rfl

theorem canonical15868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15868 raw15868Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw15868 raw15868Labels = mixedMoment B raw15868step0 raw15868step0Labels := by
      have ha : raw15868step0 = (fun i j => raw15868 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15868step0 raw15868; decide +kernel
      have hl : raw15868step0Labels = raw15868Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15868 raw15868Labels permutation168 permutation4
    mixedMoment B raw15868step0 raw15868step0Labels = mixedMoment B raw15868step1 raw15868step1Labels := by
      have ha : raw15868step1 = -raw15868step0 := by apply Matrix.ext; change ∀ i j, raw15868step1 i j = -(raw15868step0 i j); unfold raw15868step1 raw15868step0; decide +kernel
      have hl : raw15868step1Labels = raw15868step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15868step1 raw15868step1Labels = mixedMoment B raw15868step2 raw15868step2Labels := by
      have ha : raw15868step2 = raw15868step1 := by apply Matrix.ext; unfold raw15868step2 raw15868step1; decide +kernel
      have hl : raw15868step1Labels = labelEmbedding7 ∘ raw15868step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15868step1 raw15868step1Labels raw15868step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

theorem canonical15869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15869 raw15869Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw15869 raw15869Labels = mixedMoment B raw15869step0 raw15869step0Labels := by
      have ha : raw15869step0 = (fun i j => raw15869 (permutation671 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15869step0 raw15869; decide +kernel
      have hl : raw15869step0Labels = raw15869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15869 raw15869Labels permutation671 permutation2
    _ = mixedMoment B node5407 node5407Labels := by rfl

theorem canonical15870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15870 raw15870Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw15870 raw15870Labels = mixedMoment B raw15870step0 raw15870step0Labels := by
      have ha : raw15870step0 = (fun i j => raw15870 (permutation667 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15870step0 raw15870; decide +kernel
      have hl : raw15870step0Labels = raw15870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15870 raw15870Labels permutation667 permutation2
    _ = mixedMoment B node5086 node5086Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15892 raw15892Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw15892 raw15892Labels = mixedMoment B raw15892step0 raw15892step0Labels := by
      have ha : raw15892step0 = (fun i j => raw15892 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15892step0 raw15892; decide +kernel
      have hl : raw15892step0Labels = raw15892Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15892 raw15892Labels permutation682 permutation7
    mixedMoment B raw15892step0 raw15892step0Labels = mixedMoment B raw15892step1 raw15892step1Labels := by
      have ha : raw15892step1 = -raw15892step0 := by apply Matrix.ext; change ∀ i j, raw15892step1 i j = -(raw15892step0 i j); unfold raw15892step1 raw15892step0; decide +kernel
      have hl : raw15892step1Labels = raw15892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15892step1 raw15892step1Labels = mixedMoment B raw15892step2 raw15892step2Labels := by
      have ha : raw15892step2 = raw15892step1 := by apply Matrix.ext; unfold raw15892step2 raw15892step1; decide +kernel
      have hl : raw15892step1Labels = labelEmbedding1 ∘ raw15892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15892step1 raw15892step1Labels raw15892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical15893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15893 raw15893Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw15893 raw15893Labels = mixedMoment B raw15893step0 raw15893step0Labels := by
      have hz : ∀ j, raw15893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15893step0 = (fun i j => raw15893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15893step0 raw15893; decide +kernel
      have hl : raw15893step0Labels = raw15893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15893 raw15893Labels permutation434 hz
    mixedMoment B raw15893step0 raw15893step0Labels = mixedMoment B raw15893step1 raw15893step1Labels := by
      have ha : raw15893step1 = (fun i j => raw15893step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15893step1 raw15893step0; decide +kernel
      have hl : raw15893step1Labels = raw15893step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15893step0 raw15893step0Labels permutation151 permutation7
    mixedMoment B raw15893step1 raw15893step1Labels = mixedMoment B raw15893step2 raw15893step2Labels := by
      have ha : raw15893step2 = -raw15893step1 := by apply Matrix.ext; change ∀ i j, raw15893step2 i j = -(raw15893step1 i j); unfold raw15893step2 raw15893step1; decide +kernel
      have hl : raw15893step2Labels = raw15893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15893step2 raw15893step2Labels = mixedMoment B raw15893step3 raw15893step3Labels := by
      have ha : raw15893step3 = raw15893step2 := by apply Matrix.ext; unfold raw15893step3 raw15893step2; decide +kernel
      have hl : raw15893step2Labels = labelEmbedding1 ∘ raw15893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15893step2 raw15893step2Labels raw15893step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical15894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15894 raw15894Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw15894 raw15894Labels = mixedMoment B raw15894step0 raw15894step0Labels := by
      have ha : raw15894step0 = (fun i j => raw15894 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15894step0 raw15894; decide +kernel
      have hl : raw15894step0Labels = raw15894Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15894 raw15894Labels permutation682 permutation7
    mixedMoment B raw15894step0 raw15894step0Labels = mixedMoment B raw15894step1 raw15894step1Labels := by
      have ha : raw15894step1 = -raw15894step0 := by apply Matrix.ext; change ∀ i j, raw15894step1 i j = -(raw15894step0 i j); unfold raw15894step1 raw15894step0; decide +kernel
      have hl : raw15894step1Labels = raw15894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15894step1 raw15894step1Labels = mixedMoment B raw15894step2 raw15894step2Labels := by
      have ha : raw15894step2 = raw15894step1 := by apply Matrix.ext; unfold raw15894step2 raw15894step1; decide +kernel
      have hl : raw15894step1Labels = labelEmbedding1 ∘ raw15894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15894step1 raw15894step1Labels raw15894step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

theorem canonical15895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15895 raw15895Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw15895 raw15895Labels = mixedMoment B raw15895step0 raw15895step0Labels := by
      have ha : raw15895step0 = (fun i j => raw15895 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15895step0 raw15895; decide +kernel
      have hl : raw15895step0Labels = raw15895Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15895 raw15895Labels permutation263 permutation5
    mixedMoment B raw15895step0 raw15895step0Labels = mixedMoment B raw15895step1 raw15895step1Labels := by
      have ha : raw15895step1 = -raw15895step0 := by apply Matrix.ext; change ∀ i j, raw15895step1 i j = -(raw15895step0 i j); unfold raw15895step1 raw15895step0; decide +kernel
      have hl : raw15895step1Labels = raw15895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15895step1 raw15895step1Labels = mixedMoment B raw15895step2 raw15895step2Labels := by
      have ha : raw15895step2 = raw15895step1 := by apply Matrix.ext; unfold raw15895step2 raw15895step1; decide +kernel
      have hl : raw15895step1Labels = labelEmbedding1 ∘ raw15895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15895step1 raw15895step1Labels raw15895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical15896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15896 raw15896Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw15896 raw15896Labels = mixedMoment B raw15896step0 raw15896step0Labels := by
      have hz : ∀ j, raw15896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15896step0 = (fun i j => raw15896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15896step0 raw15896; decide +kernel
      have hl : raw15896step0Labels = raw15896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15896 raw15896Labels permutation434 hz
    mixedMoment B raw15896step0 raw15896step0Labels = mixedMoment B raw15896step1 raw15896step1Labels := by
      have ha : raw15896step1 = (fun i j => raw15896step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15896step1 raw15896step0; decide +kernel
      have hl : raw15896step1Labels = raw15896step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15896step0 raw15896step0Labels permutation151 permutation7
    mixedMoment B raw15896step1 raw15896step1Labels = mixedMoment B raw15896step2 raw15896step2Labels := by
      have ha : raw15896step2 = -raw15896step1 := by apply Matrix.ext; change ∀ i j, raw15896step2 i j = -(raw15896step1 i j); unfold raw15896step2 raw15896step1; decide +kernel
      have hl : raw15896step2Labels = raw15896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15896step2 raw15896step2Labels = mixedMoment B raw15896step3 raw15896step3Labels := by
      have ha : raw15896step3 = raw15896step2 := by apply Matrix.ext; unfold raw15896step3 raw15896step2; decide +kernel
      have hl : raw15896step2Labels = labelEmbedding1 ∘ raw15896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15896step2 raw15896step2Labels raw15896step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical15897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15897 raw15897Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw15897 raw15897Labels = mixedMoment B raw15897step0 raw15897step0Labels := by
      have ha : raw15897step0 = (fun i j => raw15897 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15897step0 raw15897; decide +kernel
      have hl : raw15897step0Labels = raw15897Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15897 raw15897Labels permutation682 permutation7
    mixedMoment B raw15897step0 raw15897step0Labels = mixedMoment B raw15897step1 raw15897step1Labels := by
      have ha : raw15897step1 = -raw15897step0 := by apply Matrix.ext; change ∀ i j, raw15897step1 i j = -(raw15897step0 i j); unfold raw15897step1 raw15897step0; decide +kernel
      have hl : raw15897step1Labels = raw15897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15897step1 raw15897step1Labels = mixedMoment B raw15897step2 raw15897step2Labels := by
      have ha : raw15897step2 = raw15897step1 := by apply Matrix.ext; unfold raw15897step2 raw15897step1; decide +kernel
      have hl : raw15897step1Labels = labelEmbedding1 ∘ raw15897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15897step1 raw15897step1Labels raw15897step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

theorem canonical15898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15898 raw15898Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw15898 raw15898Labels = mixedMoment B raw15898step0 raw15898step0Labels := by
      have ha : raw15898step0 = (fun i j => raw15898 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15898step0 raw15898; decide +kernel
      have hl : raw15898step0Labels = raw15898Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15898 raw15898Labels permutation261 permutation5
    mixedMoment B raw15898step0 raw15898step0Labels = mixedMoment B raw15898step1 raw15898step1Labels := by
      have ha : raw15898step1 = -raw15898step0 := by apply Matrix.ext; change ∀ i j, raw15898step1 i j = -(raw15898step0 i j); unfold raw15898step1 raw15898step0; decide +kernel
      have hl : raw15898step1Labels = raw15898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15898step1 raw15898step1Labels = mixedMoment B raw15898step2 raw15898step2Labels := by
      have ha : raw15898step2 = raw15898step1 := by apply Matrix.ext; unfold raw15898step2 raw15898step1; decide +kernel
      have hl : raw15898step1Labels = labelEmbedding1 ∘ raw15898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15898step1 raw15898step1Labels raw15898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

theorem canonical15899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15899 raw15899Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw15899 raw15899Labels = mixedMoment B raw15899step0 raw15899step0Labels := by
      have ha : raw15899step0 = (fun i j => raw15899 (permutation394 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15899step0 raw15899; decide +kernel
      have hl : raw15899step0Labels = raw15899Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15899 raw15899Labels permutation394 permutation5
    mixedMoment B raw15899step0 raw15899step0Labels = mixedMoment B raw15899step1 raw15899step1Labels := by
      have ha : raw15899step1 = raw15899step0 := by apply Matrix.ext; unfold raw15899step1 raw15899step0; decide +kernel
      have hl : raw15899step0Labels = labelEmbedding1 ∘ raw15899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15899step0 raw15899step0Labels raw15899step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

theorem canonical15900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15900 raw15900Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw15900 raw15900Labels = mixedMoment B raw15900step0 raw15900step0Labels := by
      have hz : ∀ j, raw15900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15900step0 = (fun i j => raw15900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15900step0 raw15900; decide +kernel
      have hl : raw15900step0Labels = raw15900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15900 raw15900Labels permutation434 hz
    mixedMoment B raw15900step0 raw15900step0Labels = mixedMoment B raw15900step1 raw15900step1Labels := by
      have ha : raw15900step1 = (fun i j => raw15900step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15900step1 raw15900step0; decide +kernel
      have hl : raw15900step1Labels = raw15900step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15900step0 raw15900step0Labels permutation151 permutation7
    mixedMoment B raw15900step1 raw15900step1Labels = mixedMoment B raw15900step2 raw15900step2Labels := by
      have ha : raw15900step2 = -raw15900step1 := by apply Matrix.ext; change ∀ i j, raw15900step2 i j = -(raw15900step1 i j); unfold raw15900step2 raw15900step1; decide +kernel
      have hl : raw15900step2Labels = raw15900step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15900step2 raw15900step2Labels = mixedMoment B raw15900step3 raw15900step3Labels := by
      have ha : raw15900step3 = raw15900step2 := by apply Matrix.ext; unfold raw15900step3 raw15900step2; decide +kernel
      have hl : raw15900step2Labels = labelEmbedding1 ∘ raw15900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15900step2 raw15900step2Labels raw15900step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical15901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15901 raw15901Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw15901 raw15901Labels = mixedMoment B raw15901step0 raw15901step0Labels := by
      have ha : raw15901step0 = (fun i j => raw15901 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15901step0 raw15901; decide +kernel
      have hl : raw15901step0Labels = raw15901Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15901 raw15901Labels permutation688 permutation7
    mixedMoment B raw15901step0 raw15901step0Labels = mixedMoment B raw15901step1 raw15901step1Labels := by
      have ha : raw15901step1 = -raw15901step0 := by apply Matrix.ext; change ∀ i j, raw15901step1 i j = -(raw15901step0 i j); unfold raw15901step1 raw15901step0; decide +kernel
      have hl : raw15901step1Labels = raw15901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15901step1 raw15901step1Labels = mixedMoment B raw15901step2 raw15901step2Labels := by
      have ha : raw15901step2 = raw15901step1 := by apply Matrix.ext; unfold raw15901step2 raw15901step1; decide +kernel
      have hl : raw15901step1Labels = labelEmbedding1 ∘ raw15901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15901step1 raw15901step1Labels raw15901step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

theorem canonical15902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15902 raw15902Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw15902 raw15902Labels = mixedMoment B raw15902step0 raw15902step0Labels := by
      have ha : raw15902step0 = (fun i j => raw15902 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15902step0 raw15902; decide +kernel
      have hl : raw15902step0Labels = raw15902Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15902 raw15902Labels permutation260 permutation5
    mixedMoment B raw15902step0 raw15902step0Labels = mixedMoment B raw15902step1 raw15902step1Labels := by
      have ha : raw15902step1 = -raw15902step0 := by apply Matrix.ext; change ∀ i j, raw15902step1 i j = -(raw15902step0 i j); unfold raw15902step1 raw15902step0; decide +kernel
      have hl : raw15902step1Labels = raw15902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15902step1 raw15902step1Labels = mixedMoment B raw15902step2 raw15902step2Labels := by
      have ha : raw15902step2 = raw15902step1 := by apply Matrix.ext; unfold raw15902step2 raw15902step1; decide +kernel
      have hl : raw15902step1Labels = labelEmbedding1 ∘ raw15902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15902step1 raw15902step1Labels raw15902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

theorem canonical15903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15903 raw15903Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw15903 raw15903Labels = mixedMoment B raw15903step0 raw15903step0Labels := by
      have ha : raw15903step0 = (fun i j => raw15903 (permutation480 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15903step0 raw15903; decide +kernel
      have hl : raw15903step0Labels = raw15903Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15903 raw15903Labels permutation480 permutation5
    mixedMoment B raw15903step0 raw15903step0Labels = mixedMoment B raw15903step1 raw15903step1Labels := by
      have ha : raw15903step1 = raw15903step0 := by apply Matrix.ext; unfold raw15903step1 raw15903step0; decide +kernel
      have hl : raw15903step0Labels = labelEmbedding1 ∘ raw15903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15903step0 raw15903step0Labels raw15903step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

theorem canonical15904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15904 raw15904Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw15904 raw15904Labels = mixedMoment B raw15904step0 raw15904step0Labels := by
      have ha : raw15904step0 = (fun i j => raw15904 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15904step0 raw15904; decide +kernel
      have hl : raw15904step0Labels = raw15904Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15904 raw15904Labels permutation682 permutation7
    mixedMoment B raw15904step0 raw15904step0Labels = mixedMoment B raw15904step1 raw15904step1Labels := by
      have ha : raw15904step1 = -raw15904step0 := by apply Matrix.ext; change ∀ i j, raw15904step1 i j = -(raw15904step0 i j); unfold raw15904step1 raw15904step0; decide +kernel
      have hl : raw15904step1Labels = raw15904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15904step1 raw15904step1Labels = mixedMoment B raw15904step2 raw15904step2Labels := by
      have ha : raw15904step2 = raw15904step1 := by apply Matrix.ext; unfold raw15904step2 raw15904step1; decide +kernel
      have hl : raw15904step1Labels = labelEmbedding1 ∘ raw15904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15904step1 raw15904step1Labels raw15904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

theorem canonical15905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15905 raw15905Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw15905 raw15905Labels = mixedMoment B raw15905step0 raw15905step0Labels := by
      have ha : raw15905step0 = (fun i j => raw15905 (permutation250 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15905step0 raw15905; decide +kernel
      have hl : raw15905step0Labels = raw15905Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15905 raw15905Labels permutation250 permutation5
    mixedMoment B raw15905step0 raw15905step0Labels = mixedMoment B raw15905step1 raw15905step1Labels := by
      have ha : raw15905step1 = -raw15905step0 := by apply Matrix.ext; change ∀ i j, raw15905step1 i j = -(raw15905step0 i j); unfold raw15905step1 raw15905step0; decide +kernel
      have hl : raw15905step1Labels = raw15905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15905step1 raw15905step1Labels = mixedMoment B raw15905step2 raw15905step2Labels := by
      have ha : raw15905step2 = raw15905step1 := by apply Matrix.ext; unfold raw15905step2 raw15905step1; decide +kernel
      have hl : raw15905step1Labels = labelEmbedding1 ∘ raw15905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15905step1 raw15905step1Labels raw15905step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical15906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15906 raw15906Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw15906 raw15906Labels = mixedMoment B raw15906step0 raw15906step0Labels := by
      have ha : raw15906step0 = (fun i j => raw15906 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15906step0 raw15906; decide +kernel
      have hl : raw15906step0Labels = raw15906Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15906 raw15906Labels permutation682 permutation7
    mixedMoment B raw15906step0 raw15906step0Labels = mixedMoment B raw15906step1 raw15906step1Labels := by
      have ha : raw15906step1 = -raw15906step0 := by apply Matrix.ext; change ∀ i j, raw15906step1 i j = -(raw15906step0 i j); unfold raw15906step1 raw15906step0; decide +kernel
      have hl : raw15906step1Labels = raw15906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15906step1 raw15906step1Labels = mixedMoment B raw15906step2 raw15906step2Labels := by
      have ha : raw15906step2 = raw15906step1 := by apply Matrix.ext; unfold raw15906step2 raw15906step1; decide +kernel
      have hl : raw15906step1Labels = labelEmbedding1 ∘ raw15906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15906step1 raw15906step1Labels raw15906step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical15907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15907 raw15907Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw15907 raw15907Labels = mixedMoment B raw15907step0 raw15907step0Labels := by
      have ha : raw15907step0 = (fun i j => raw15907 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15907step0 raw15907; decide +kernel
      have hl : raw15907step0Labels = raw15907Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15907 raw15907Labels permutation682 permutation7
    mixedMoment B raw15907step0 raw15907step0Labels = mixedMoment B raw15907step1 raw15907step1Labels := by
      have ha : raw15907step1 = -raw15907step0 := by apply Matrix.ext; change ∀ i j, raw15907step1 i j = -(raw15907step0 i j); unfold raw15907step1 raw15907step0; decide +kernel
      have hl : raw15907step1Labels = raw15907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15907step1 raw15907step1Labels = mixedMoment B raw15907step2 raw15907step2Labels := by
      have ha : raw15907step2 = raw15907step1 := by apply Matrix.ext; unfold raw15907step2 raw15907step1; decide +kernel
      have hl : raw15907step1Labels = labelEmbedding1 ∘ raw15907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15907step1 raw15907step1Labels raw15907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical15908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15908 raw15908Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw15908 raw15908Labels = mixedMoment B raw15908step0 raw15908step0Labels := by
      have ha : raw15908step0 = (fun i j => raw15908 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15908step0 raw15908; decide +kernel
      have hl : raw15908step0Labels = raw15908Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15908 raw15908Labels permutation668 permutation2
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical15909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15909 raw15909Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw15909 raw15909Labels = mixedMoment B raw15909step0 raw15909step0Labels := by
      have ha : raw15909step0 = (fun i j => raw15909 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15909step0 raw15909; decide +kernel
      have hl : raw15909step0Labels = raw15909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15909 raw15909Labels permutation674 permutation2
    _ = mixedMoment B node3805 node3805Labels := by rfl

theorem canonical15910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15910 raw15910Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw15910 raw15910Labels = mixedMoment B raw15910step0 raw15910step0Labels := by
      have hz : ∀ j, raw15910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15910step0 = (fun i j => raw15910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15910step0 raw15910; decide +kernel
      have hl : raw15910step0Labels = raw15910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15910 raw15910Labels permutation346 hz
    mixedMoment B raw15910step0 raw15910step0Labels = mixedMoment B raw15910step1 raw15910step1Labels := by
      have ha : raw15910step1 = (fun i j => raw15910step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15910step1 raw15910step0; decide +kernel
      have hl : raw15910step1Labels = raw15910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15910step0 raw15910step0Labels permutation151 permutation2
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical15911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15911 raw15911Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw15911 raw15911Labels = mixedMoment B raw15911step0 raw15911step0Labels := by
      have hz : ∀ j, raw15911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15911step0 = (fun i j => raw15911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15911step0 raw15911; decide +kernel
      have hl : raw15911step0Labels = raw15911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15911 raw15911Labels permutation434 hz
    mixedMoment B raw15911step0 raw15911step0Labels = mixedMoment B raw15911step1 raw15911step1Labels := by
      have ha : raw15911step1 = (fun i j => raw15911step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15911step1 raw15911step0; decide +kernel
      have hl : raw15911step1Labels = raw15911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15911step0 raw15911step0Labels permutation151 permutation2
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical15912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15912 raw15912Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw15912 raw15912Labels = mixedMoment B raw15912step0 raw15912step0Labels := by
      have ha : raw15912step0 = (fun i j => raw15912 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15912step0 raw15912; decide +kernel
      have hl : raw15912step0Labels = raw15912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15912 raw15912Labels permutation682 permutation2
    _ = mixedMoment B node2508 node2508Labels := by rfl

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

theorem canonical2121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2121 raw2121Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw2121 raw2121Labels = mixedMoment B raw2121step0 raw2121step0Labels := by
      have ha : raw2121step0 = (fun i j => raw2121 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2121step0 raw2121; decide +kernel
      have hl : raw2121step0Labels = raw2121Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2121 raw2121Labels permutation152 permutation4
    mixedMoment B raw2121step0 raw2121step0Labels = mixedMoment B raw2121step1 raw2121step1Labels := by
      have ha : raw2121step1 = raw2121step0 := by apply Matrix.ext; unfold raw2121step1 raw2121step0; decide +kernel
      have hl : raw2121step0Labels = labelEmbedding7 ∘ raw2121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2121step0 raw2121step0Labels raw2121step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

theorem canonical2122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2122 raw2122Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw2122 raw2122Labels = mixedMoment B raw2122step0 raw2122step0Labels := by
      have ha : raw2122step0 = (fun i j => raw2122 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2122step0 raw2122; decide +kernel
      have hl : raw2122step0Labels = raw2122Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2122 raw2122Labels permutation152 permutation4
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical2123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2123 raw2123Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw2123 raw2123Labels = mixedMoment B raw2123step0 raw2123step0Labels := by
      have ha : raw2123step0 = (fun i j => raw2123 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2123step0 raw2123; decide +kernel
      have hl : raw2123step0Labels = raw2123Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2123 raw2123Labels permutation152 permutation6
    mixedMoment B raw2123step0 raw2123step0Labels = mixedMoment B raw2123step1 raw2123step1Labels := by
      have ha : raw2123step1 = -raw2123step0 := by apply Matrix.ext; change ∀ i j, raw2123step1 i j = -(raw2123step0 i j); unfold raw2123step1 raw2123step0; decide +kernel
      have hl : raw2123step1Labels = raw2123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2123step1 raw2123step1Labels = mixedMoment B raw2123step2 raw2123step2Labels := by
      have ha : raw2123step2 = raw2123step1 := by apply Matrix.ext; unfold raw2123step2 raw2123step1; decide +kernel
      have hl : raw2123step1Labels = labelEmbedding1 ∘ raw2123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2123step1 raw2123step1Labels raw2123step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

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

theorem canonical2412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2412 raw2412Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw2412 raw2412Labels = mixedMoment B raw2412step0 raw2412step0Labels := by
      have ha : raw2412step0 = (fun i j => raw2412 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2412step0 raw2412; decide +kernel
      have hl : raw2412step0Labels = raw2412Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2412 raw2412Labels permutation152 permutation4
    mixedMoment B raw2412step0 raw2412step0Labels = mixedMoment B raw2412step1 raw2412step1Labels := by
      have ha : raw2412step1 = raw2412step0 := by apply Matrix.ext; unfold raw2412step1 raw2412step0; decide +kernel
      have hl : raw2412step0Labels = labelEmbedding7 ∘ raw2412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2412step0 raw2412step0Labels raw2412step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

theorem canonical2413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2413 raw2413Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw2413 raw2413Labels = mixedMoment B raw2413step0 raw2413step0Labels := by
      have ha : raw2413step0 = (fun i j => raw2413 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2413step0 raw2413; decide +kernel
      have hl : raw2413step0Labels = raw2413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2413 raw2413Labels permutation152 permutation4
    _ = mixedMoment B node3703 node3703Labels := by rfl

theorem canonical2414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2414 raw2414Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw2414 raw2414Labels = mixedMoment B raw2414step0 raw2414step0Labels := by
      have ha : raw2414step0 = (fun i j => raw2414 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2414step0 raw2414; decide +kernel
      have hl : raw2414step0Labels = raw2414Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2414 raw2414Labels permutation152 permutation6
    mixedMoment B raw2414step0 raw2414step0Labels = mixedMoment B raw2414step1 raw2414step1Labels := by
      have ha : raw2414step1 = -raw2414step0 := by apply Matrix.ext; change ∀ i j, raw2414step1 i j = -(raw2414step0 i j); unfold raw2414step1 raw2414step0; decide +kernel
      have hl : raw2414step1Labels = raw2414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2414step1 raw2414step1Labels = mixedMoment B raw2414step2 raw2414step2Labels := by
      have ha : raw2414step2 = raw2414step1 := by apply Matrix.ext; unfold raw2414step2 raw2414step1; decide +kernel
      have hl : raw2414step1Labels = labelEmbedding1 ∘ raw2414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2414step1 raw2414step1Labels raw2414step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

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

theorem canonical2484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2484 raw2484Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw2484 raw2484Labels = mixedMoment B raw2484step0 raw2484step0Labels := by
      have ha : raw2484step0 = (fun i j => raw2484 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2484step0 raw2484; decide +kernel
      have hl : raw2484step0Labels = raw2484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2484 raw2484Labels permutation152 permutation4
    mixedMoment B raw2484step0 raw2484step0Labels = mixedMoment B raw2484step1 raw2484step1Labels := by
      have ha : raw2484step1 = raw2484step0 := by apply Matrix.ext; unfold raw2484step1 raw2484step0; decide +kernel
      have hl : raw2484step0Labels = labelEmbedding7 ∘ raw2484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2484step0 raw2484step0Labels raw2484step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2485 raw2485Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw2485 raw2485Labels = mixedMoment B raw2485step0 raw2485step0Labels := by
      have ha : raw2485step0 = (fun i j => raw2485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2485step0 raw2485; decide +kernel
      have hl : raw2485step0Labels = raw2485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2485 raw2485Labels permutation152 permutation4
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2486 raw2486Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw2486 raw2486Labels = mixedMoment B raw2486step0 raw2486step0Labels := by
      have ha : raw2486step0 = (fun i j => raw2486 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2486step0 raw2486; decide +kernel
      have hl : raw2486step0Labels = raw2486Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2486 raw2486Labels permutation164 permutation6
    mixedMoment B raw2486step0 raw2486step0Labels = mixedMoment B raw2486step1 raw2486step1Labels := by
      have ha : raw2486step1 = -raw2486step0 := by apply Matrix.ext; change ∀ i j, raw2486step1 i j = -(raw2486step0 i j); unfold raw2486step1 raw2486step0; decide +kernel
      have hl : raw2486step1Labels = raw2486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2486step1 raw2486step1Labels = mixedMoment B raw2486step2 raw2486step2Labels := by
      have ha : raw2486step2 = raw2486step1 := by apply Matrix.ext; unfold raw2486step2 raw2486step1; decide +kernel
      have hl : raw2486step1Labels = labelEmbedding1 ∘ raw2486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2486step1 raw2486step1Labels raw2486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

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

theorem canonical2490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2490 raw2490Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2490 raw2490Labels = mixedMoment B raw2490step0 raw2490step0Labels := by
      have ha : raw2490step0 = (fun i j => raw2490 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2490step0 raw2490; decide +kernel
      have hl : raw2490step0Labels = raw2490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2490 raw2490Labels permutation32 permutation4
    mixedMoment B raw2490step0 raw2490step0Labels = mixedMoment B raw2490step1 raw2490step1Labels := by
      have ha : raw2490step1 = raw2490step0 := by apply Matrix.ext; unfold raw2490step1 raw2490step0; decide +kernel
      have hl : raw2490step0Labels = labelEmbedding7 ∘ raw2490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2490step0 raw2490step0Labels raw2490step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical2491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2491 raw2491Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2491 raw2491Labels = mixedMoment B raw2491step0 raw2491step0Labels := by
      have ha : raw2491step0 = (fun i j => raw2491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2491step0 raw2491; decide +kernel
      have hl : raw2491step0Labels = raw2491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2491 raw2491Labels permutation32 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical2492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2492 raw2492Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw2492 raw2492Labels = mixedMoment B raw2492step0 raw2492step0Labels := by
      have ha : raw2492step0 = (fun i j => raw2492 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2492step0 raw2492; decide +kernel
      have hl : raw2492step0Labels = raw2492Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2492 raw2492Labels permutation36 permutation6
    mixedMoment B raw2492step0 raw2492step0Labels = mixedMoment B raw2492step1 raw2492step1Labels := by
      have ha : raw2492step1 = -raw2492step0 := by apply Matrix.ext; change ∀ i j, raw2492step1 i j = -(raw2492step0 i j); unfold raw2492step1 raw2492step0; decide +kernel
      have hl : raw2492step1Labels = raw2492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2492step1 raw2492step1Labels = mixedMoment B raw2492step2 raw2492step2Labels := by
      have ha : raw2492step2 = raw2492step1 := by apply Matrix.ext; unfold raw2492step2 raw2492step1; decide +kernel
      have hl : raw2492step1Labels = labelEmbedding1 ∘ raw2492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2492step1 raw2492step1Labels raw2492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2493 raw2493Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2493 raw2493Labels = mixedMoment B raw2493step0 raw2493step0Labels := by
      have ha : raw2493step0 = (fun i j => raw2493 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2493step0 raw2493; decide +kernel
      have hl : raw2493step0Labels = raw2493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2493 raw2493Labels permutation32 permutation4
    mixedMoment B raw2493step0 raw2493step0Labels = mixedMoment B raw2493step1 raw2493step1Labels := by
      have ha : raw2493step1 = raw2493step0 := by apply Matrix.ext; unfold raw2493step1 raw2493step0; decide +kernel
      have hl : raw2493step0Labels = labelEmbedding7 ∘ raw2493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2493step0 raw2493step0Labels raw2493step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2494 raw2494Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2494 raw2494Labels = mixedMoment B raw2494step0 raw2494step0Labels := by
      have ha : raw2494step0 = (fun i j => raw2494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2494step0 raw2494; decide +kernel
      have hl : raw2494step0Labels = raw2494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2494 raw2494Labels permutation32 permutation4
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2495 raw2495Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2495 raw2495Labels = mixedMoment B raw2495step0 raw2495step0Labels := by
      have ha : raw2495step0 = (fun i j => raw2495 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2495step0 raw2495; decide +kernel
      have hl : raw2495step0Labels = raw2495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2495 raw2495Labels permutation37 permutation6
    mixedMoment B raw2495step0 raw2495step0Labels = mixedMoment B raw2495step1 raw2495step1Labels := by
      have ha : raw2495step1 = -raw2495step0 := by apply Matrix.ext; change ∀ i j, raw2495step1 i j = -(raw2495step0 i j); unfold raw2495step1 raw2495step0; decide +kernel
      have hl : raw2495step1Labels = raw2495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2495step1 raw2495step1Labels = mixedMoment B raw2495step2 raw2495step2Labels := by
      have ha : raw2495step2 = raw2495step1 := by apply Matrix.ext; unfold raw2495step2 raw2495step1; decide +kernel
      have hl : raw2495step1Labels = labelEmbedding1 ∘ raw2495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2495step1 raw2495step1Labels raw2495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5098 node5098Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2508 node2508Labels + mixedMoment B node3460 node3460Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2121 singletonSmall5098
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5098) = raw2121Labels := by decide +kernel
  rw [hl, canonical2121 B hB] at h
  have hc0 : mixedMoment B raw2121 (Fin.cases (0 : Fin 2) singletonSmall5098) =
      mixedMoment B node2508 node2508Labels := by
    have ha : raw2121 = raw2122 := by apply Matrix.ext; unfold raw2121 raw2122; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5098 = raw2122Labels := by decide +kernel
    rw [ha, hj, canonical2122 B hB]
  have hc1 : mixedMoment B raw2121 (Fin.cases (1 : Fin 2) singletonSmall5098) =
      mixedMoment B node3460 node3460Labels := by
    have ha : raw2121 = raw2123 := by apply Matrix.ext; unfold raw2121 raw2123; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5098 = raw2123Labels := by decide +kernel
    rw [ha, hj, canonical2123 B hB]
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

theorem singleton5365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5365 node5365Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3703 node3703Labels + mixedMoment B node3758 node3758Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2412 singletonSmall5365
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5365) = raw2412Labels := by decide +kernel
  rw [hl, canonical2412 B hB] at h
  have hc0 : mixedMoment B raw2412 (Fin.cases (0 : Fin 2) singletonSmall5365) =
      mixedMoment B node3703 node3703Labels := by
    have ha : raw2412 = raw2413 := by apply Matrix.ext; unfold raw2412 raw2413; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5365 = raw2413Labels := by decide +kernel
    rw [ha, hj, canonical2413 B hB]
  have hc1 : mixedMoment B raw2412 (Fin.cases (1 : Fin 2) singletonSmall5365) =
      mixedMoment B node3758 node3758Labels := by
    have ha : raw2412 = raw2414 := by apply Matrix.ext; unfold raw2412 raw2414; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5365 = raw2414Labels := by decide +kernel
    rw [ha, hj, canonical2414 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton5405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5405 node5405Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3800 node3800Labels + mixedMoment B node3805 node3805Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2484 singletonSmall5405
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5405) = raw2484Labels := by decide +kernel
  rw [hl, canonical2484 B hB] at h
  have hc0 : mixedMoment B raw2484 (Fin.cases (0 : Fin 2) singletonSmall5405) =
      mixedMoment B node3800 node3800Labels := by
    have ha : raw2484 = raw2485 := by apply Matrix.ext; unfold raw2484 raw2485; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5405 = raw2485Labels := by decide +kernel
    rw [ha, hj, canonical2485 B hB]
  have hc1 : mixedMoment B raw2484 (Fin.cases (1 : Fin 2) singletonSmall5405) =
      mixedMoment B node3805 node3805Labels := by
    have ha : raw2484 = raw2486 := by apply Matrix.ext; unfold raw2484 raw2486; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5405 = raw2486Labels := by decide +kernel
    rw [ha, hj, canonical2486 B hB]
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

theorem singleton5411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5411 node5411Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3809 node3809Labels + mixedMoment B node3813 node3813Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2490 singletonSmall5411
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5411) = raw2490Labels := by decide +kernel
  rw [hl, canonical2490 B hB] at h
  have hc0 : mixedMoment B raw2490 (Fin.cases (0 : Fin 2) singletonSmall5411) =
      mixedMoment B node3809 node3809Labels := by
    have ha : raw2490 = raw2491 := by apply Matrix.ext; unfold raw2490 raw2491; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5411 = raw2491Labels := by decide +kernel
    rw [ha, hj, canonical2491 B hB]
  have hc1 : mixedMoment B raw2490 (Fin.cases (1 : Fin 2) singletonSmall5411) =
      mixedMoment B node3813 node3813Labels := by
    have ha : raw2490 = raw2492 := by apply Matrix.ext; unfold raw2490 raw2492; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5411 = raw2492Labels := by decide +kernel
    rw [ha, hj, canonical2492 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5412 node5412Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3814 node3814Labels + mixedMoment B node3814 node3814Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2493 singletonSmall5412
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5412) = raw2493Labels := by decide +kernel
  rw [hl, canonical2493 B hB] at h
  have hc0 : mixedMoment B raw2493 (Fin.cases (0 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2494 := by apply Matrix.ext; unfold raw2493 raw2494; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5412 = raw2494Labels := by decide +kernel
    rw [ha, hj, canonical2494 B hB]
  have hc1 : mixedMoment B raw2493 (Fin.cases (1 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2495 := by apply Matrix.ext; unfold raw2493 raw2495; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5412 = raw2495Labels := by decide +kernel
    rw [ha, hj, canonical2495 B hB]
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

theorem sound3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3814 node3814Labels = Sparse.eval nodeValue3814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3814) = mixedMoment B node3814 node3814Labels := rfl
  simpa [nodeValue3814, Sparse.eval] using hc.symm

theorem sound5412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5412 node5412Labels = Sparse.eval nodeValue5412 (mixedVector B) := by
  have h := singleton5412 B _hB
  rw [sound3814 B _hB _hF] at h
  norm_num [nodeValue5412, nodeValue3814, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2508 node2508Labels = Sparse.eval nodeValue2508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2508) = mixedMoment B node2508 node2508Labels := rfl
  simpa [nodeValue2508, Sparse.eval] using hc.symm

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

theorem sound2606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2606 node2606Labels = Sparse.eval nodeValue2606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2606) = mixedMoment B node2606 node2606Labels := rfl
  simpa [nodeValue2606, Sparse.eval] using hc.symm

theorem sound2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2607 node2607Labels = Sparse.eval nodeValue2607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2607) = mixedMoment B node2607 node2607Labels := rfl
  simpa [nodeValue2607, Sparse.eval] using hc.symm

theorem sound2614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2614 node2614Labels = Sparse.eval nodeValue2614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2614) = mixedMoment B node2614 node2614Labels := rfl
  simpa [nodeValue2614, Sparse.eval] using hc.symm

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

theorem sound2630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2630 node2630Labels = Sparse.eval nodeValue2630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2630) = mixedMoment B node2630 node2630Labels := rfl
  simpa [nodeValue2630, Sparse.eval] using hc.symm

theorem sound2631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2631 node2631Labels = Sparse.eval nodeValue2631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2631) = mixedMoment B node2631 node2631Labels := rfl
  simpa [nodeValue2631, Sparse.eval] using hc.symm

theorem sound2676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2676 node2676Labels = Sparse.eval nodeValue2676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2676) = mixedMoment B node2676 node2676Labels := rfl
  simpa [nodeValue2676, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2858 node2858Labels = Sparse.eval nodeValue2858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2858) = mixedMoment B node2858 node2858Labels := rfl
  simpa [nodeValue2858, Sparse.eval] using hc.symm

theorem sound2859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2859 node2859Labels = Sparse.eval nodeValue2859 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2859) = mixedMoment B node2859 node2859Labels := rfl
  simpa [nodeValue2859, Sparse.eval] using hc.symm

theorem sound2864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2864 node2864Labels = Sparse.eval nodeValue2864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2864) = mixedMoment B node2864 node2864Labels := rfl
  simpa [nodeValue2864, Sparse.eval] using hc.symm

theorem sound2869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2869 node2869Labels = Sparse.eval nodeValue2869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2869) = mixedMoment B node2869 node2869Labels := rfl
  simpa [nodeValue2869, Sparse.eval] using hc.symm

theorem sound2870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2870 node2870Labels = Sparse.eval nodeValue2870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2870) = mixedMoment B node2870 node2870Labels := rfl
  simpa [nodeValue2870, Sparse.eval] using hc.symm

theorem sound2878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2878 node2878Labels = Sparse.eval nodeValue2878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2878) = mixedMoment B node2878 node2878Labels := rfl
  simpa [nodeValue2878, Sparse.eval] using hc.symm

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

theorem sound3016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3016 node3016Labels = Sparse.eval nodeValue3016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3016) = mixedMoment B node3016 node3016Labels := rfl
  simpa [nodeValue3016, Sparse.eval] using hc.symm

theorem sound3023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3023 node3023Labels = Sparse.eval nodeValue3023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3023) = mixedMoment B node3023 node3023Labels := rfl
  simpa [nodeValue3023, Sparse.eval] using hc.symm

theorem sound3030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3030 node3030Labels = Sparse.eval nodeValue3030 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3030) = mixedMoment B node3030 node3030Labels := rfl
  simpa [nodeValue3030, Sparse.eval] using hc.symm

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

theorem sound3043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3043 node3043Labels = Sparse.eval nodeValue3043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3043) = mixedMoment B node3043 node3043Labels := rfl
  simpa [nodeValue3043, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = 0 := by
  exact mixedMoment_alpha B hF node3085 node3085Labels 2 permutation158
    (by decide +kernel)

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

theorem sound3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = Sparse.eval nodeValue3085 (mixedVector B) := by
  simpa only [nodeValue3085, Sparse.eval_nil] using zero3085 B _hB _hF

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

theorem sound3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3460 node3460Labels = Sparse.eval nodeValue3460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3460) = mixedMoment B node3460 node3460Labels := rfl
  simpa [nodeValue3460, Sparse.eval] using hc.symm

theorem sound3461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3461 node3461Labels = Sparse.eval nodeValue3461 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3461) = mixedMoment B node3461 node3461Labels := rfl
  simpa [nodeValue3461, Sparse.eval] using hc.symm

theorem sound3464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3464 node3464Labels = Sparse.eval nodeValue3464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3464) = mixedMoment B node3464 node3464Labels := rfl
  simpa [nodeValue3464, Sparse.eval] using hc.symm

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

theorem zero3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = 0 := by
  exact mixedMoment_alpha B hF node3525 node3525Labels 1 permutation434
    (by decide +kernel)

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

theorem sound3524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3524 node3524Labels = Sparse.eval nodeValue3524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3524) = mixedMoment B node3524 node3524Labels := rfl
  simpa [nodeValue3524, Sparse.eval] using hc.symm

theorem sound3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = Sparse.eval nodeValue3525 (mixedVector B) := by
  simpa only [nodeValue3525, Sparse.eval_nil] using zero3525 B _hB _hF

theorem sound3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3526 node3526Labels = Sparse.eval nodeValue3526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3526) = mixedMoment B node3526 node3526Labels := rfl
  simpa [nodeValue3526, Sparse.eval] using hc.symm

theorem sound3527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3527 node3527Labels = Sparse.eval nodeValue3527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3527) = mixedMoment B node3527 node3527Labels := rfl
  simpa [nodeValue3527, Sparse.eval] using hc.symm

theorem sound3566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3566 node3566Labels = Sparse.eval nodeValue3566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3566) = mixedMoment B node3566 node3566Labels := rfl
  simpa [nodeValue3566, Sparse.eval] using hc.symm

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

theorem sound3697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3697 node3697Labels = Sparse.eval nodeValue3697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3697) = mixedMoment B node3697 node3697Labels := rfl
  simpa [nodeValue3697, Sparse.eval] using hc.symm

theorem sound3703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3703 node3703Labels = Sparse.eval nodeValue3703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3703) = mixedMoment B node3703 node3703Labels := rfl
  simpa [nodeValue3703, Sparse.eval] using hc.symm

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

theorem sound3758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3758 node3758Labels = Sparse.eval nodeValue3758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3758) = mixedMoment B node3758 node3758Labels := rfl
  simpa [nodeValue3758, Sparse.eval] using hc.symm

theorem sound3759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3759 node3759Labels = Sparse.eval nodeValue3759 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3759) = mixedMoment B node3759 node3759Labels := rfl
  simpa [nodeValue3759, Sparse.eval] using hc.symm

theorem sound3762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3762 node3762Labels = Sparse.eval nodeValue3762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3762) = mixedMoment B node3762 node3762Labels := rfl
  simpa [nodeValue3762, Sparse.eval] using hc.symm

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

theorem zero3808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = 0 := by
  exact mixedMoment_order_one B hB node3808 node3808Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = 0 := by
  exact mixedMoment_order_one B hB node3816 node3816Labels 1
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

theorem sound3780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3780 node3780Labels = Sparse.eval nodeValue3780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3780) = mixedMoment B node3780 node3780Labels := rfl
  simpa [nodeValue3780, Sparse.eval] using hc.symm

theorem sound3786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3786 node3786Labels = Sparse.eval nodeValue3786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3786) = mixedMoment B node3786 node3786Labels := rfl
  simpa [nodeValue3786, Sparse.eval] using hc.symm

theorem sound3788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3788 node3788Labels = Sparse.eval nodeValue3788 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3788) = mixedMoment B node3788 node3788Labels := rfl
  simpa [nodeValue3788, Sparse.eval] using hc.symm

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

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

theorem sound3802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3802 node3802Labels = Sparse.eval nodeValue3802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3802) = mixedMoment B node3802 node3802Labels := rfl
  simpa [nodeValue3802, Sparse.eval] using hc.symm

theorem sound3803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3803 node3803Labels = Sparse.eval nodeValue3803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3803) = mixedMoment B node3803 node3803Labels := rfl
  simpa [nodeValue3803, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

theorem sound3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = Sparse.eval nodeValue3808 (mixedVector B) := by
  simpa only [nodeValue3808, Sparse.eval_nil] using zero3808 B _hB _hF

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

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

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3854 node3854Labels = Sparse.eval nodeValue3854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3854) = mixedMoment B node3854 node3854Labels := rfl
  simpa [nodeValue3854, Sparse.eval] using hc.symm

theorem sound3874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3874 node3874Labels = Sparse.eval nodeValue3874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3874) = mixedMoment B node3874 node3874Labels := rfl
  simpa [nodeValue3874, Sparse.eval] using hc.symm

theorem sound3878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3878 node3878Labels = Sparse.eval nodeValue3878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3878) = mixedMoment B node3878 node3878Labels := rfl
  simpa [nodeValue3878, Sparse.eval] using hc.symm

theorem sound3881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3881 node3881Labels = Sparse.eval nodeValue3881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3881) = mixedMoment B node3881 node3881Labels := rfl
  simpa [nodeValue3881, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

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

theorem zero3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = 0 := by
  exact mixedMoment_alpha B hF node3956 node3956Labels 1 permutation203
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

theorem sound3954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3954 node3954Labels = Sparse.eval nodeValue3954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3954) = mixedMoment B node3954 node3954Labels := rfl
  simpa [nodeValue3954, Sparse.eval] using hc.symm

theorem sound3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = Sparse.eval nodeValue3956 (mixedVector B) := by
  simpa only [nodeValue3956, Sparse.eval_nil] using zero3956 B _hB _hF

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

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

theorem zero3976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3976 node3976Labels = 0 := by
  exact mixedMoment_alpha B hF node3976 node3976Labels 2 permutation160
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

theorem sound3976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3976 node3976Labels = Sparse.eval nodeValue3976 (mixedVector B) := by
  simpa only [nodeValue3976, Sparse.eval_nil] using zero3976 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5085 node5085Labels = Sparse.eval nodeValue5085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5085) = mixedMoment B node5085 node5085Labels := rfl
  simpa [nodeValue5085, Sparse.eval] using hc.symm

theorem sound5086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5086 node5086Labels = Sparse.eval nodeValue5086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5086) = mixedMoment B node5086 node5086Labels := rfl
  simpa [nodeValue5086, Sparse.eval] using hc.symm

theorem sound5098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5098 node5098Labels = Sparse.eval nodeValue5098 (mixedVector B) := by
  have h := singleton5098 B _hB
  rw [sound2508 B _hB _hF, sound3460 B _hB _hF] at h
  norm_num [nodeValue5098, nodeValue2508, nodeValue3460, Sparse.eval] at h ⊢
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

theorem zero5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = 0 := by
  exact mixedMoment_alpha B hF node5256 node5256Labels 1 permutation203
    (by decide +kernel)

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

theorem sound5254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5254 node5254Labels = Sparse.eval nodeValue5254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5254) = mixedMoment B node5254 node5254Labels := rfl
  simpa [nodeValue5254, Sparse.eval] using hc.symm

theorem sound5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = Sparse.eval nodeValue5256 (mixedVector B) := by
  simpa only [nodeValue5256, Sparse.eval_nil] using zero5256 B _hB _hF

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

theorem sound5286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5286 node5286Labels = Sparse.eval nodeValue5286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5286) = mixedMoment B node5286 node5286Labels := rfl
  simpa [nodeValue5286, Sparse.eval] using hc.symm

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

theorem sound5359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5359 node5359Labels = Sparse.eval nodeValue5359 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5359) = mixedMoment B node5359 node5359Labels := rfl
  simpa [nodeValue5359, Sparse.eval] using hc.symm

theorem sound5360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5360 node5360Labels = Sparse.eval nodeValue5360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5360) = mixedMoment B node5360 node5360Labels := rfl
  simpa [nodeValue5360, Sparse.eval] using hc.symm

theorem sound5365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5365 node5365Labels = Sparse.eval nodeValue5365 (mixedVector B) := by
  have h := singleton5365 B _hB
  rw [sound3703 B _hB _hF, sound3758 B _hB _hF] at h
  norm_num [nodeValue5365, nodeValue3703, nodeValue3758, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = 0 := by
  exact mixedMoment_order_one B hB node5410 node5410Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5405 node5405Labels = Sparse.eval nodeValue5405 (mixedVector B) := by
  have h := singleton5405 B _hB
  rw [sound3800 B _hB _hF, sound3805 B _hB _hF] at h
  norm_num [nodeValue5405, nodeValue3800, nodeValue3805, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5407 node5407Labels = Sparse.eval nodeValue5407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5407) = mixedMoment B node5407 node5407Labels := rfl
  simpa [nodeValue5407, Sparse.eval] using hc.symm

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

theorem sound5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5411 node5411Labels = Sparse.eval nodeValue5411 (mixedVector B) := by
  have h := singleton5411 B _hB
  rw [sound3809 B _hB _hF, sound3813 B _hB _hF] at h
  norm_num [nodeValue5411, nodeValue3809, nodeValue3813, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5429 node5429Labels = Sparse.eval nodeValue5429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5429) = mixedMoment B node5429 node5429Labels := rfl
  simpa [nodeValue5429, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources29
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm952 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA952 + difference 5 0) (sourceB952 + difference 0 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2858) := by
    have ha : (tripleCharges (sourceA952 + difference 5 0) (sourceB952 + difference 0 5) sourceC952) = raw15644 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15644; decide +kernel
    rw [ha]
    exact (canonical15644 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA952 + difference 5 1) (sourceB952 + difference 1 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2859) := by
    have ha : (tripleCharges (sourceA952 + difference 5 1) (sourceB952 + difference 1 5) sourceC952) = raw15652 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15652; decide +kernel
    rw [ha]
    exact (canonical15652 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA952 + difference 5 2) (sourceB952 + difference 2 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA952 + difference 5 2) (sourceB952 + difference 2 5) sourceC952) = raw15658 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15658; decide +kernel
    rw [ha]
    exact (canonical15658 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA952 + difference 5 3) (sourceB952 + difference 3 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA952 + difference 5 3) (sourceB952 + difference 3 5) sourceC952) = raw15663 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15663; decide +kernel
    rw [ha]
    exact (canonical15663 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA952 + difference 5 4) (sourceB952 + difference 4 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA952 + difference 5 4) (sourceB952 + difference 4 5) sourceC952) = raw15662 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15662; decide +kernel
    rw [ha]
    exact (canonical15662 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA952 + difference 5 5) (sourceB952 + difference 5 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA952 + difference 5 5) (sourceB952 + difference 5 5) sourceC952) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA952 + sourceB952) sourceC952) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA952 + sourceB952) sourceC952) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA952 sourceB952 sourceC952 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA952 sourceB952 sourceC952
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm952, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq954 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm954 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA954 + difference 0 1) (sourceB954 + difference 1 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA954 + difference 0 1) (sourceB954 + difference 1 0) sourceC954) = raw15685 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15685; decide +kernel
    rw [ha]
    exact (canonical15685 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA954 + difference 0 2) (sourceB954 + difference 2 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA954 + difference 0 2) (sourceB954 + difference 2 0) sourceC954) = raw15686 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15686; decide +kernel
    rw [ha]
    exact (canonical15686 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA954 + difference 0 3) (sourceB954 + difference 3 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA954 + difference 0 3) (sourceB954 + difference 3 0) sourceC954) = raw15687 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15687; decide +kernel
    rw [ha]
    exact (canonical15687 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA954 + difference 0 4) (sourceB954 + difference 4 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA954 + difference 0 4) (sourceB954 + difference 4 0) sourceC954) = raw15688 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15688; decide +kernel
    rw [ha]
    exact (canonical15688 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA954 + difference 0 5) (sourceB954 + difference 5 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3938) := by
    have ha : (tripleCharges (sourceA954 + difference 0 5) (sourceB954 + difference 5 0) sourceC954) = raw15689 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15689; decide +kernel
    rw [ha]
    exact (canonical15689 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA954 + difference 1 0) (sourceB954 + difference 0 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3566) := by
    have ha : (tripleCharges (sourceA954 + difference 1 0) (sourceB954 + difference 0 1) sourceC954) = raw15690 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15690; decide +kernel
    rw [ha]
    exact (canonical15690 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA954 + difference 1 2) (sourceB954 + difference 2 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA954 + difference 1 2) (sourceB954 + difference 2 1) sourceC954) = raw15691 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15691; decide +kernel
    rw [ha]
    exact (canonical15691 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA954 + difference 1 3) (sourceB954 + difference 3 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA954 + difference 1 3) (sourceB954 + difference 3 1) sourceC954) = raw15692 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15692; decide +kernel
    rw [ha]
    exact (canonical15692 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA954 + difference 1 4) (sourceB954 + difference 4 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2607) := by
    have ha : (tripleCharges (sourceA954 + difference 1 4) (sourceB954 + difference 4 1) sourceC954) = raw15693 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15693; decide +kernel
    rw [ha]
    exact (canonical15693 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA954 + difference 1 5) (sourceB954 + difference 5 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA954 + difference 1 5) (sourceB954 + difference 5 1) sourceC954) = raw15694 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15694; decide +kernel
    rw [ha]
    exact (canonical15694 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA954 + difference 2 0) (sourceB954 + difference 0 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA954 + difference 2 0) (sourceB954 + difference 0 2) sourceC954) = raw15695 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15695; decide +kernel
    rw [ha]
    exact (canonical15695 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA954 + difference 2 1) (sourceB954 + difference 1 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA954 + difference 2 1) (sourceB954 + difference 1 2) sourceC954) = raw15696 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15696; decide +kernel
    rw [ha]
    exact (canonical15696 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA954 + difference 2 3) (sourceB954 + difference 3 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA954 + difference 2 3) (sourceB954 + difference 3 2) sourceC954) = raw15697 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15697; decide +kernel
    rw [ha]
    exact (canonical15697 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA954 + difference 2 4) (sourceB954 + difference 4 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2606) := by
    have ha : (tripleCharges (sourceA954 + difference 2 4) (sourceB954 + difference 4 2) sourceC954) = raw15698 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15698; decide +kernel
    rw [ha]
    exact (canonical15698 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA954 + difference 2 5) (sourceB954 + difference 5 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA954 + difference 2 5) (sourceB954 + difference 5 2) sourceC954) = raw15699 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15699; decide +kernel
    rw [ha]
    exact (canonical15699 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA954 + difference 3 0) (sourceB954 + difference 0 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA954 + difference 3 0) (sourceB954 + difference 0 3) sourceC954) = raw15700 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15700; decide +kernel
    rw [ha]
    exact (canonical15700 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA954 + difference 3 1) (sourceB954 + difference 1 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA954 + difference 3 1) (sourceB954 + difference 1 3) sourceC954) = raw15701 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15701; decide +kernel
    rw [ha]
    exact (canonical15701 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA954 + difference 3 2) (sourceB954 + difference 2 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA954 + difference 3 2) (sourceB954 + difference 2 3) sourceC954) = raw15702 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15702; decide +kernel
    rw [ha]
    exact (canonical15702 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA954 + difference 3 4) (sourceB954 + difference 4 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2606) := by
    have ha : (tripleCharges (sourceA954 + difference 3 4) (sourceB954 + difference 4 3) sourceC954) = raw15703 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15703; decide +kernel
    rw [ha]
    exact (canonical15703 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA954 + difference 3 5) (sourceB954 + difference 5 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA954 + difference 3 5) (sourceB954 + difference 5 3) sourceC954) = raw15704 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15704; decide +kernel
    rw [ha]
    exact (canonical15704 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA954 + difference 4 0) (sourceB954 + difference 0 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA954 + difference 4 0) (sourceB954 + difference 0 4) sourceC954) = raw15705 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15705; decide +kernel
    rw [ha]
    exact (canonical15705 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA954 + difference 4 1) (sourceB954 + difference 1 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA954 + difference 4 1) (sourceB954 + difference 1 4) sourceC954) = raw15706 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15706; decide +kernel
    rw [ha]
    exact (canonical15706 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA954 + difference 4 2) (sourceB954 + difference 2 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA954 + difference 4 2) (sourceB954 + difference 2 4) sourceC954) = raw15707 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15707; decide +kernel
    rw [ha]
    exact (canonical15707 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA954 + difference 4 3) (sourceB954 + difference 3 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA954 + difference 4 3) (sourceB954 + difference 3 4) sourceC954) = raw15708 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15708; decide +kernel
    rw [ha]
    exact (canonical15708 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA954 + difference 4 5) (sourceB954 + difference 5 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA954 + difference 4 5) (sourceB954 + difference 5 4) sourceC954) = raw15709 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15709; decide +kernel
    rw [ha]
    exact (canonical15709 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA954 + difference 5 0) (sourceB954 + difference 0 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA954 + difference 5 0) (sourceB954 + difference 0 5) sourceC954) = raw15710 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15710; decide +kernel
    rw [ha]
    exact (canonical15710 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA954 + difference 5 1) (sourceB954 + difference 1 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA954 + difference 5 1) (sourceB954 + difference 1 5) sourceC954) = raw15711 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15711; decide +kernel
    rw [ha]
    exact (canonical15711 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA954 + difference 5 2) (sourceB954 + difference 2 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA954 + difference 5 2) (sourceB954 + difference 2 5) sourceC954) = raw15712 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15712; decide +kernel
    rw [ha]
    exact (canonical15712 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA954 + difference 5 3) (sourceB954 + difference 3 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA954 + difference 5 3) (sourceB954 + difference 3 5) sourceC954) = raw15713 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15713; decide +kernel
    rw [ha]
    exact (canonical15713 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA954 + difference 5 4) (sourceB954 + difference 4 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA954 + difference 5 4) (sourceB954 + difference 4 5) sourceC954) = raw15714 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15714; decide +kernel
    rw [ha]
    exact (canonical15714 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA954 sourceB954 sourceC954
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm954, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq956 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm956 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA956 + difference 0 0) (sourceB956 + difference 0 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA956 + difference 0 0) (sourceB956 + difference 0 0) sourceC956) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA956 + difference 0 1) (sourceB956 + difference 1 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA956 + difference 0 1) (sourceB956 + difference 1 0) sourceC956) = raw15738 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15738; decide +kernel
    rw [ha]
    exact (canonical15738 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA956 + difference 0 2) (sourceB956 + difference 2 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA956 + difference 0 2) (sourceB956 + difference 2 0) sourceC956) = raw15739 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15739; decide +kernel
    rw [ha]
    exact (canonical15739 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA956 + difference 0 3) (sourceB956 + difference 3 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA956 + difference 0 3) (sourceB956 + difference 3 0) sourceC956) = raw15740 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15740; decide +kernel
    rw [ha]
    exact (canonical15740 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA956 + difference 0 4) (sourceB956 + difference 4 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA956 + difference 0 4) (sourceB956 + difference 4 0) sourceC956) = raw15741 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15741; decide +kernel
    rw [ha]
    exact (canonical15741 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA956 + difference 0 5) (sourceB956 + difference 5 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3703) := by
    have ha : (tripleCharges (sourceA956 + difference 0 5) (sourceB956 + difference 5 0) sourceC956) = raw15742 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15742; decide +kernel
    rw [ha]
    exact (canonical15742 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA956 + sourceB956) sourceC956) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA956 + sourceB956) sourceC956) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA956 sourceB956 sourceC956 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA956 sourceB956 sourceC956
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm956, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq957 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm957 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA957 + difference 1 0) (sourceB957 + difference 0 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2630) := by
    have ha : (tripleCharges (sourceA957 + difference 1 0) (sourceB957 + difference 0 1) sourceC957) = raw15743 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15743; decide +kernel
    rw [ha]
    exact (canonical15743 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA957 + difference 1 1) (sourceB957 + difference 1 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA957 + difference 1 1) (sourceB957 + difference 1 1) sourceC957) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA957 + difference 1 2) (sourceB957 + difference 2 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA957 + difference 1 2) (sourceB957 + difference 2 1) sourceC957) = raw15744 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15744; decide +kernel
    rw [ha]
    exact (canonical15744 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA957 + difference 1 3) (sourceB957 + difference 3 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA957 + difference 1 3) (sourceB957 + difference 3 1) sourceC957) = raw15745 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15745; decide +kernel
    rw [ha]
    exact (canonical15745 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA957 + difference 1 4) (sourceB957 + difference 4 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2869) := by
    have ha : (tripleCharges (sourceA957 + difference 1 4) (sourceB957 + difference 4 1) sourceC957) = raw15746 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15746; decide +kernel
    rw [ha]
    exact (canonical15746 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA957 + difference 1 5) (sourceB957 + difference 5 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3697) := by
    have ha : (tripleCharges (sourceA957 + difference 1 5) (sourceB957 + difference 5 1) sourceC957) = raw15747 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15747; decide +kernel
    rw [ha]
    exact (canonical15747 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA957 + sourceB957) sourceC957) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA957 + sourceB957) sourceC957) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA957 sourceB957 sourceC957 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA957 sourceB957 sourceC957
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm957, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq958 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm958 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA958 + difference 0 1) (sourceB958 + difference 1 0) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA958 + difference 0 1) (sourceB958 + difference 1 0) sourceC958) = raw15738 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15738; decide +kernel
    rw [ha]
    exact (canonical15738 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA958 + difference 1 1) (sourceB958 + difference 1 1) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA958 + difference 1 1) (sourceB958 + difference 1 1) sourceC958) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA958 + difference 2 1) (sourceB958 + difference 1 2) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA958 + difference 2 1) (sourceB958 + difference 1 2) sourceC958) = raw15748 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15748; decide +kernel
    rw [ha]
    exact (canonical15748 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA958 + difference 3 1) (sourceB958 + difference 1 3) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA958 + difference 3 1) (sourceB958 + difference 1 3) sourceC958) = raw15749 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15749; decide +kernel
    rw [ha]
    exact (canonical15749 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA958 + difference 4 1) (sourceB958 + difference 1 4) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA958 + difference 4 1) (sourceB958 + difference 1 4) sourceC958) = raw15750 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15750; decide +kernel
    rw [ha]
    exact (canonical15750 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA958 + difference 5 1) (sourceB958 + difference 1 5) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3786) := by
    have ha : (tripleCharges (sourceA958 + difference 5 1) (sourceB958 + difference 1 5) sourceC958) = raw15751 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15751; decide +kernel
    rw [ha]
    exact (canonical15751 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA958 + sourceB958) sourceC958) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA958 + sourceB958) sourceC958) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA958 sourceB958 sourceC958 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA958 sourceB958 sourceC958
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm958, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq959 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm959 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA959 + difference 0 4) (sourceB959 + difference 4 0) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA959 + difference 0 4) (sourceB959 + difference 4 0) sourceC959) = raw15741 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15741; decide +kernel
    rw [ha]
    exact (canonical15741 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA959 + difference 1 4) (sourceB959 + difference 4 1) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2869) := by
    have ha : (tripleCharges (sourceA959 + difference 1 4) (sourceB959 + difference 4 1) sourceC959) = raw15746 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15746; decide +kernel
    rw [ha]
    exact (canonical15746 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA959 + difference 2 4) (sourceB959 + difference 4 2) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2870) := by
    have ha : (tripleCharges (sourceA959 + difference 2 4) (sourceB959 + difference 4 2) sourceC959) = raw15752 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15752; decide +kernel
    rw [ha]
    exact (canonical15752 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA959 + difference 3 4) (sourceB959 + difference 4 3) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2870) := by
    have ha : (tripleCharges (sourceA959 + difference 3 4) (sourceB959 + difference 4 3) sourceC959) = raw15753 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15753; decide +kernel
    rw [ha]
    exact (canonical15753 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA959 + difference 4 4) (sourceB959 + difference 4 4) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA959 + difference 4 4) (sourceB959 + difference 4 4) sourceC959) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA959 + difference 5 4) (sourceB959 + difference 4 5) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA959 + difference 5 4) (sourceB959 + difference 4 5) sourceC959) = raw15754 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15754; decide +kernel
    rw [ha]
    exact (canonical15754 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA959 + sourceB959) sourceC959) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA959 + sourceB959) sourceC959) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA959 sourceB959 sourceC959 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA959 sourceB959 sourceC959
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm959, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

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

theorem sourceEq960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm960 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA960 + difference 5 0) (sourceB960 + difference 0 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA960 + difference 5 0) (sourceB960 + difference 0 5) sourceC960) = raw15755 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15755; decide +kernel
    rw [ha]
    exact (canonical15755 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA960 + difference 5 1) (sourceB960 + difference 1 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3786) := by
    have ha : (tripleCharges (sourceA960 + difference 5 1) (sourceB960 + difference 1 5) sourceC960) = raw15751 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15751; decide +kernel
    rw [ha]
    exact (canonical15751 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA960 + difference 5 2) (sourceB960 + difference 2 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA960 + difference 5 2) (sourceB960 + difference 2 5) sourceC960) = raw15756 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15756; decide +kernel
    rw [ha]
    exact (canonical15756 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA960 + difference 5 3) (sourceB960 + difference 3 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA960 + difference 5 3) (sourceB960 + difference 3 5) sourceC960) = raw15757 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15757; decide +kernel
    rw [ha]
    exact (canonical15757 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA960 + difference 5 4) (sourceB960 + difference 4 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA960 + difference 5 4) (sourceB960 + difference 4 5) sourceC960) = raw15754 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15754; decide +kernel
    rw [ha]
    exact (canonical15754 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA960 + difference 5 5) (sourceB960 + difference 5 5) sourceC960) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA960 + difference 5 5) (sourceB960 + difference 5 5) sourceC960) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA960 sourceB960 sourceC960 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA960 + sourceB960) sourceC960) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA960 + sourceB960) sourceC960) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA960 sourceB960 sourceC960 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA960 sourceB960 sourceC960
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm960, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq966 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm966 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA966 + difference 0 1) (sourceB966 + difference 1 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA966 + difference 0 1) (sourceB966 + difference 1 0) sourceC966) = raw15858 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15858; decide +kernel
    rw [ha]
    exact (canonical15858 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA966 + difference 0 2) (sourceB966 + difference 2 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA966 + difference 0 2) (sourceB966 + difference 2 0) sourceC966) = raw15117 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15117; decide +kernel
    rw [ha]
    exact (canonical15117 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA966 + difference 0 3) (sourceB966 + difference 3 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA966 + difference 0 3) (sourceB966 + difference 3 0) sourceC966) = raw15859 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15859; decide +kernel
    rw [ha]
    exact (canonical15859 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA966 + difference 0 4) (sourceB966 + difference 4 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA966 + difference 0 4) (sourceB966 + difference 4 0) sourceC966) = raw15667 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15667; decide +kernel
    rw [ha]
    exact (canonical15667 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA966 + difference 0 5) (sourceB966 + difference 5 0) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA966 + difference 0 5) (sourceB966 + difference 5 0) sourceC966) = raw15860 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15860; decide +kernel
    rw [ha]
    exact (canonical15860 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA966 + difference 1 0) (sourceB966 + difference 0 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA966 + difference 1 0) (sourceB966 + difference 0 1) sourceC966) = raw15861 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15861; decide +kernel
    rw [ha]
    exact (canonical15861 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA966 + difference 1 2) (sourceB966 + difference 2 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA966 + difference 1 2) (sourceB966 + difference 2 1) sourceC966) = raw15122 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15122; decide +kernel
    rw [ha]
    exact (canonical15122 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA966 + difference 1 3) (sourceB966 + difference 3 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA966 + difference 1 3) (sourceB966 + difference 3 1) sourceC966) = raw15862 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15862; decide +kernel
    rw [ha]
    exact (canonical15862 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA966 + difference 1 4) (sourceB966 + difference 4 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA966 + difference 1 4) (sourceB966 + difference 4 1) sourceC966) = raw15671 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15671; decide +kernel
    rw [ha]
    exact (canonical15671 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA966 + difference 1 5) (sourceB966 + difference 5 1) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA966 + difference 1 5) (sourceB966 + difference 5 1) sourceC966) = raw15863 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15863; decide +kernel
    rw [ha]
    exact (canonical15863 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA966 + difference 2 0) (sourceB966 + difference 0 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA966 + difference 2 0) (sourceB966 + difference 0 2) sourceC966) = raw15864 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15864; decide +kernel
    rw [ha]
    exact (canonical15864 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA966 + difference 2 1) (sourceB966 + difference 1 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA966 + difference 2 1) (sourceB966 + difference 1 2) sourceC966) = raw15865 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15865; decide +kernel
    rw [ha]
    exact (canonical15865 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA966 + difference 2 3) (sourceB966 + difference 3 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA966 + difference 2 3) (sourceB966 + difference 3 2) sourceC966) = raw15866 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15866; decide +kernel
    rw [ha]
    exact (canonical15866 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA966 + difference 2 4) (sourceB966 + difference 4 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA966 + difference 2 4) (sourceB966 + difference 4 2) sourceC966) = raw15676 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15676; decide +kernel
    rw [ha]
    exact (canonical15676 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA966 + difference 2 5) (sourceB966 + difference 5 2) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA966 + difference 2 5) (sourceB966 + difference 5 2) sourceC966) = raw15867 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15867; decide +kernel
    rw [ha]
    exact (canonical15867 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA966 + difference 3 0) (sourceB966 + difference 0 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA966 + difference 3 0) (sourceB966 + difference 0 3) sourceC966) = raw15868 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15868; decide +kernel
    rw [ha]
    exact (canonical15868 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA966 + difference 3 1) (sourceB966 + difference 1 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA966 + difference 3 1) (sourceB966 + difference 1 3) sourceC966) = raw15869 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15869; decide +kernel
    rw [ha]
    exact (canonical15869 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA966 + difference 3 2) (sourceB966 + difference 2 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA966 + difference 3 2) (sourceB966 + difference 2 3) sourceC966) = raw15132 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15132; decide +kernel
    rw [ha]
    exact (canonical15132 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA966 + difference 3 4) (sourceB966 + difference 4 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA966 + difference 3 4) (sourceB966 + difference 4 3) sourceC966) = raw15680 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15680; decide +kernel
    rw [ha]
    exact (canonical15680 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA966 + difference 3 5) (sourceB966 + difference 5 3) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA966 + difference 3 5) (sourceB966 + difference 5 3) sourceC966) = raw15870 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15870; decide +kernel
    rw [ha]
    exact (canonical15870 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA966 + difference 4 0) (sourceB966 + difference 0 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA966 + difference 4 0) (sourceB966 + difference 0 4) sourceC966) = raw15204 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15204; decide +kernel
    rw [ha]
    exact (canonical15204 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA966 + difference 4 1) (sourceB966 + difference 1 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA966 + difference 4 1) (sourceB966 + difference 1 4) sourceC966) = raw15205 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15205; decide +kernel
    rw [ha]
    exact (canonical15205 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA966 + difference 4 2) (sourceB966 + difference 2 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA966 + difference 4 2) (sourceB966 + difference 2 4) sourceC966) = raw14714 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw14714; decide +kernel
    rw [ha]
    exact (canonical14714 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA966 + difference 4 3) (sourceB966 + difference 3 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA966 + difference 4 3) (sourceB966 + difference 3 4) sourceC966) = raw14984 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw14984; decide +kernel
    rw [ha]
    exact (canonical14984 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA966 + difference 4 5) (sourceB966 + difference 5 4) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA966 + difference 4 5) (sourceB966 + difference 5 4) sourceC966) = raw15206 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15206; decide +kernel
    rw [ha]
    exact (canonical15206 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA966 + difference 5 0) (sourceB966 + difference 0 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA966 + difference 5 0) (sourceB966 + difference 0 5) sourceC966) = raw15123 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15123; decide +kernel
    rw [ha]
    exact (canonical15123 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA966 + difference 5 1) (sourceB966 + difference 1 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA966 + difference 5 1) (sourceB966 + difference 1 5) sourceC966) = raw15124 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15124; decide +kernel
    rw [ha]
    exact (canonical15124 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA966 + difference 5 2) (sourceB966 + difference 2 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA966 + difference 5 2) (sourceB966 + difference 2 5) sourceC966) = raw15210 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15210; decide +kernel
    rw [ha]
    exact (canonical15210 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA966 + difference 5 3) (sourceB966 + difference 3 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA966 + difference 5 3) (sourceB966 + difference 3 5) sourceC966) = raw15125 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15125; decide +kernel
    rw [ha]
    exact (canonical15125 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA966 + difference 5 4) (sourceB966 + difference 4 5) sourceC966) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA966 + difference 5 4) (sourceB966 + difference 4 5) sourceC966) = raw15126 := by
      apply Matrix.ext; unfold tripleCharges sourceA966 sourceB966 sourceC966 difference raw15126; decide +kernel
    rw [ha]
    exact (canonical15126 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA966 sourceB966 sourceC966
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm966, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm968 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA968 + difference 0 1) (sourceB968 + difference 1 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA968 + difference 0 1) (sourceB968 + difference 1 0) sourceC968) = raw15892 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15892; decide +kernel
    rw [ha]
    exact (canonical15892 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA968 + difference 0 2) (sourceB968 + difference 2 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA968 + difference 0 2) (sourceB968 + difference 2 0) sourceC968) = raw15144 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15144; decide +kernel
    rw [ha]
    exact (canonical15144 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA968 + difference 0 3) (sourceB968 + difference 3 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA968 + difference 0 3) (sourceB968 + difference 3 0) sourceC968) = raw15893 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15893; decide +kernel
    rw [ha]
    exact (canonical15893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA968 + difference 0 4) (sourceB968 + difference 4 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA968 + difference 0 4) (sourceB968 + difference 4 0) sourceC968) = raw15718 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15718; decide +kernel
    rw [ha]
    exact (canonical15718 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA968 + difference 0 5) (sourceB968 + difference 5 0) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA968 + difference 0 5) (sourceB968 + difference 5 0) sourceC968) = raw15894 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15894; decide +kernel
    rw [ha]
    exact (canonical15894 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA968 + difference 1 0) (sourceB968 + difference 0 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA968 + difference 1 0) (sourceB968 + difference 0 1) sourceC968) = raw15895 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15895; decide +kernel
    rw [ha]
    exact (canonical15895 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA968 + difference 1 2) (sourceB968 + difference 2 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA968 + difference 1 2) (sourceB968 + difference 2 1) sourceC968) = raw15149 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15149; decide +kernel
    rw [ha]
    exact (canonical15149 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA968 + difference 1 3) (sourceB968 + difference 3 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA968 + difference 1 3) (sourceB968 + difference 3 1) sourceC968) = raw15896 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15896; decide +kernel
    rw [ha]
    exact (canonical15896 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA968 + difference 1 4) (sourceB968 + difference 4 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA968 + difference 1 4) (sourceB968 + difference 4 1) sourceC968) = raw15722 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15722; decide +kernel
    rw [ha]
    exact (canonical15722 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA968 + difference 1 5) (sourceB968 + difference 5 1) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA968 + difference 1 5) (sourceB968 + difference 5 1) sourceC968) = raw15897 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15897; decide +kernel
    rw [ha]
    exact (canonical15897 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA968 + difference 2 0) (sourceB968 + difference 0 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA968 + difference 2 0) (sourceB968 + difference 0 2) sourceC968) = raw15898 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15898; decide +kernel
    rw [ha]
    exact (canonical15898 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA968 + difference 2 1) (sourceB968 + difference 1 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA968 + difference 2 1) (sourceB968 + difference 1 2) sourceC968) = raw15899 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15899; decide +kernel
    rw [ha]
    exact (canonical15899 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA968 + difference 2 3) (sourceB968 + difference 3 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA968 + difference 2 3) (sourceB968 + difference 3 2) sourceC968) = raw15900 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15900; decide +kernel
    rw [ha]
    exact (canonical15900 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA968 + difference 2 4) (sourceB968 + difference 4 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA968 + difference 2 4) (sourceB968 + difference 4 2) sourceC968) = raw15727 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15727; decide +kernel
    rw [ha]
    exact (canonical15727 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA968 + difference 2 5) (sourceB968 + difference 5 2) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA968 + difference 2 5) (sourceB968 + difference 5 2) sourceC968) = raw15901 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15901; decide +kernel
    rw [ha]
    exact (canonical15901 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA968 + difference 3 0) (sourceB968 + difference 0 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA968 + difference 3 0) (sourceB968 + difference 0 3) sourceC968) = raw15902 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15902; decide +kernel
    rw [ha]
    exact (canonical15902 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA968 + difference 3 1) (sourceB968 + difference 1 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA968 + difference 3 1) (sourceB968 + difference 1 3) sourceC968) = raw15903 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15903; decide +kernel
    rw [ha]
    exact (canonical15903 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA968 + difference 3 2) (sourceB968 + difference 2 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA968 + difference 3 2) (sourceB968 + difference 2 3) sourceC968) = raw15159 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15159; decide +kernel
    rw [ha]
    exact (canonical15159 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA968 + difference 3 4) (sourceB968 + difference 4 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA968 + difference 3 4) (sourceB968 + difference 4 3) sourceC968) = raw15731 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15731; decide +kernel
    rw [ha]
    exact (canonical15731 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA968 + difference 3 5) (sourceB968 + difference 5 3) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA968 + difference 3 5) (sourceB968 + difference 5 3) sourceC968) = raw15904 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15904; decide +kernel
    rw [ha]
    exact (canonical15904 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA968 + difference 4 0) (sourceB968 + difference 0 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA968 + difference 4 0) (sourceB968 + difference 0 4) sourceC968) = raw15905 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15905; decide +kernel
    rw [ha]
    exact (canonical15905 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA968 + difference 4 1) (sourceB968 + difference 1 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA968 + difference 4 1) (sourceB968 + difference 1 4) sourceC968) = raw15906 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15906; decide +kernel
    rw [ha]
    exact (canonical15906 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA968 + difference 4 2) (sourceB968 + difference 2 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA968 + difference 4 2) (sourceB968 + difference 2 4) sourceC968) = raw14774 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw14774; decide +kernel
    rw [ha]
    exact (canonical14774 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA968 + difference 4 3) (sourceB968 + difference 3 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA968 + difference 4 3) (sourceB968 + difference 3 4) sourceC968) = raw15006 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15006; decide +kernel
    rw [ha]
    exact (canonical15006 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA968 + difference 4 5) (sourceB968 + difference 5 4) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA968 + difference 4 5) (sourceB968 + difference 5 4) sourceC968) = raw15907 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15907; decide +kernel
    rw [ha]
    exact (canonical15907 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA968 + difference 5 0) (sourceB968 + difference 0 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA968 + difference 5 0) (sourceB968 + difference 0 5) sourceC968) = raw15150 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15150; decide +kernel
    rw [ha]
    exact (canonical15150 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA968 + difference 5 1) (sourceB968 + difference 1 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA968 + difference 5 1) (sourceB968 + difference 1 5) sourceC968) = raw15151 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15151; decide +kernel
    rw [ha]
    exact (canonical15151 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA968 + difference 5 2) (sourceB968 + difference 2 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA968 + difference 5 2) (sourceB968 + difference 2 5) sourceC968) = raw15732 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15732; decide +kernel
    rw [ha]
    exact (canonical15732 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA968 + difference 5 3) (sourceB968 + difference 3 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA968 + difference 5 3) (sourceB968 + difference 3 5) sourceC968) = raw15152 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15152; decide +kernel
    rw [ha]
    exact (canonical15152 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA968 + difference 5 4) (sourceB968 + difference 4 5) sourceC968) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA968 + difference 5 4) (sourceB968 + difference 4 5) sourceC968) = raw15153 := by
      apply Matrix.ext; unfold tripleCharges sourceA968 sourceB968 sourceC968 difference raw15153; decide +kernel
    rw [ha]
    exact (canonical15153 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA968 sourceB968 sourceC968
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm968, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm969 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA969 + difference 0 0) (sourceB969 + difference 0 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA969 + difference 0 0) (sourceB969 + difference 0 0) sourceC969) = raw15908 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15908; decide +kernel
    rw [ha]
    exact (canonical15908 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA969 + difference 0 1) (sourceB969 + difference 1 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA969 + difference 0 1) (sourceB969 + difference 1 0) sourceC969) = raw15909 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15909; decide +kernel
    rw [ha]
    exact (canonical15909 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA969 + difference 0 2) (sourceB969 + difference 2 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA969 + difference 0 2) (sourceB969 + difference 2 0) sourceC969) = raw15910 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15910; decide +kernel
    rw [ha]
    exact (canonical15910 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA969 + difference 0 3) (sourceB969 + difference 3 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA969 + difference 0 3) (sourceB969 + difference 3 0) sourceC969) = raw15911 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15911; decide +kernel
    rw [ha]
    exact (canonical15911 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA969 + difference 0 4) (sourceB969 + difference 4 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3703) := by
    have ha : (tripleCharges (sourceA969 + difference 0 4) (sourceB969 + difference 4 0) sourceC969) = raw15742 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15742; decide +kernel
    rw [ha]
    exact (canonical15742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA969 + difference 0 5) (sourceB969 + difference 5 0) sourceC969) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA969 + difference 0 5) (sourceB969 + difference 5 0) sourceC969) = raw15912 := by
      apply Matrix.ext; unfold tripleCharges sourceA969 sourceB969 sourceC969 difference raw15912; decide +kernel
    rw [ha]
    exact (canonical15912 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA969 + sourceB969) sourceC969) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA969 + sourceB969) sourceC969) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA969 sourceB969 sourceC969 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA969 sourceB969 sourceC969
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm969, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck832 : Integer.Sparse.reindex keyMap MixedData.row832 = numericRow832 := by decide +kernel

theorem numericCheck832 (x : Master → ℝ) : Integer.Sparse.eval numericRow832 x =
    (1 : ℝ) * reducedSource832 x := by
  norm_num [numericRow832, reducedSource832, Integer.Sparse.eval, Sparse.eval, nodeValue2858, nodeValue2859, nodeValue2864, nodeValue3030, nodeValue3954, nodeValue4091]

theorem reindexCheck833 : Integer.Sparse.reindex keyMap MixedData.row833 = numericRow833 := by decide +kernel

theorem numericCheck833 (x : Master → ℝ) : Integer.Sparse.eval numericRow833 x =
    (4320 : ℝ) * reducedSource833 x := by
  norm_num [numericRow833, reducedSource833, Integer.Sparse.eval, Sparse.eval, nodeValue2606, nodeValue2607, nodeValue2631, nodeValue2676, nodeValue3524, nodeValue3525, nodeValue3527, nodeValue3566, nodeValue3780, nodeValue3799, nodeValue3800, nodeValue3802, nodeValue3847, nodeValue3850, nodeValue3852, nodeValue3854, nodeValue3878, nodeValue3881, nodeValue3938, nodeValue3976, nodeValue3995]
  ring

theorem reindexCheck835 : Integer.Sparse.reindex keyMap MixedData.row835 = numericRow835 := by decide +kernel

theorem numericCheck835 (x : Master → ℝ) : Integer.Sparse.eval numericRow835 x =
    (1 : ℝ) * reducedSource835 x := by
  norm_num [numericRow835, reducedSource835, Integer.Sparse.eval, Sparse.eval, nodeValue2878, nodeValue3703, nodeValue3874, nodeValue3956, nodeValue3961, nodeValue4092]

theorem reindexCheck836 : Integer.Sparse.reindex keyMap MixedData.row836 = numericRow836 := by decide +kernel

theorem numericCheck836 (x : Master → ℝ) : Integer.Sparse.eval numericRow836 x =
    (1 : ℝ) * reducedSource836 x := by
  norm_num [numericRow836, reducedSource836, Integer.Sparse.eval, Sparse.eval, nodeValue2630, nodeValue2869, nodeValue3697, nodeValue3874, nodeValue3884, nodeValue4092]

theorem reindexCheck837 : Integer.Sparse.reindex keyMap MixedData.row837 = numericRow837 := by decide +kernel

theorem numericCheck837 (x : Master → ℝ) : Integer.Sparse.eval numericRow837 x =
    (1 : ℝ) * reducedSource837 x := by
  norm_num [numericRow837, reducedSource837, Integer.Sparse.eval, Sparse.eval, nodeValue3786, nodeValue3788, nodeValue3805, nodeValue3874, nodeValue3956, nodeValue4092]

theorem reindexCheck838 : Integer.Sparse.reindex keyMap MixedData.row838 = numericRow838 := by decide +kernel

theorem numericCheck838 (x : Master → ℝ) : Integer.Sparse.eval numericRow838 x =
    (1 : ℝ) * reducedSource838 x := by
  norm_num [numericRow838, reducedSource838, Integer.Sparse.eval, Sparse.eval, nodeValue2869, nodeValue2870, nodeValue2878, nodeValue3043, nodeValue3874, nodeValue4092]

theorem reindexCheck839 : Integer.Sparse.reindex keyMap MixedData.row839 = numericRow839 := by decide +kernel

theorem numericCheck839 (x : Master → ℝ) : Integer.Sparse.eval numericRow839 x =
    (1 : ℝ) * reducedSource839 x := by
  norm_num [numericRow839, reducedSource839, Integer.Sparse.eval, Sparse.eval, nodeValue2614, nodeValue3043, nodeValue3786, nodeValue3850, nodeValue3874, nodeValue4092]

theorem reindexCheck843 : Integer.Sparse.reindex keyMap MixedData.row843 = numericRow843 := by decide +kernel

theorem numericCheck843 (x : Master → ℝ) : Integer.Sparse.eval numericRow843 x =
    (8640 : ℝ) * reducedSource843 x := by
  norm_num [numericRow843, reducedSource843, Integer.Sparse.eval, Sparse.eval, nodeValue5085, nodeValue5086, nodeValue5098, nodeValue5254, nodeValue5256, nodeValue5265, nodeValue5286, nodeValue5359, nodeValue5360, nodeValue5365, nodeValue5405, nodeValue5406, nodeValue5407, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5429, nodeValue5434, nodeValue5435]
  ring

theorem reindexCheck845 : Integer.Sparse.reindex keyMap MixedData.row845 = numericRow845 := by decide +kernel

theorem numericCheck845 (x : Master → ℝ) : Integer.Sparse.eval numericRow845 x =
    (2160 : ℝ) * reducedSource845 x := by
  norm_num [numericRow845, reducedSource845, Integer.Sparse.eval, Sparse.eval, nodeValue3016, nodeValue3023, nodeValue3037, nodeValue3085, nodeValue3460, nodeValue3461, nodeValue3464, nodeValue3526, nodeValue3758, nodeValue3759, nodeValue3762, nodeValue3800, nodeValue3803, nodeValue3808, nodeValue3809, nodeValue3814, nodeValue3847, nodeValue3853, nodeValue3954, nodeValue3977, nodeValue3982]
  ring

theorem reindexCheck846 : Integer.Sparse.reindex keyMap MixedData.row846 = numericRow846 := by decide +kernel

theorem numericCheck846 (x : Master → ℝ) : Integer.Sparse.eval numericRow846 x =
    (1 : ℝ) * reducedSource846 x := by
  norm_num [numericRow846, reducedSource846, Integer.Sparse.eval, Sparse.eval, nodeValue2508, nodeValue3703, nodeValue3805, nodeValue3812, nodeValue3816, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource832 (mixedVector B) = 0 := by
  have h2858 : mixedVector B (Sum.inr 2858) = Sparse.eval nodeValue2858 (mixedVector B) := by
    change mixedMoment B node2858 node2858Labels = _
    exact sound2858 B hB hF
  have h2859 : mixedVector B (Sum.inr 2859) = Sparse.eval nodeValue2859 (mixedVector B) := by
    change mixedMoment B node2859 node2859Labels = _
    exact sound2859 B hB hF
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h3030 : mixedVector B (Sum.inr 3030) = Sparse.eval nodeValue3030 (mixedVector B) := by
    change mixedMoment B node3030 node3030Labels = _
    exact sound3030 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm952, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2858, h2859, h2864, h3030, h3954, h4091, reducedSource832] using sourceEq952 B hB

theorem rowSound832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row832 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck832, numericCheck832, reducedZero832 B hB hF, mul_zero]

theorem reducedZero833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource833 (mixedVector B) = 0 := by
  have h2606 : mixedVector B (Sum.inr 2606) = Sparse.eval nodeValue2606 (mixedVector B) := by
    change mixedMoment B node2606 node2606Labels = _
    exact sound2606 B hB hF
  have h2607 : mixedVector B (Sum.inr 2607) = Sparse.eval nodeValue2607 (mixedVector B) := by
    change mixedMoment B node2607 node2607Labels = _
    exact sound2607 B hB hF
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h3524 : mixedVector B (Sum.inr 3524) = Sparse.eval nodeValue3524 (mixedVector B) := by
    change mixedMoment B node3524 node3524Labels = _
    exact sound3524 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3527 : mixedVector B (Sum.inr 3527) = Sparse.eval nodeValue3527 (mixedVector B) := by
    change mixedMoment B node3527 node3527Labels = _
    exact sound3527 B hB hF
  have h3566 : mixedVector B (Sum.inr 3566) = Sparse.eval nodeValue3566 (mixedVector B) := by
    change mixedMoment B node3566 node3566Labels = _
    exact sound3566 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3802 : mixedVector B (Sum.inr 3802) = Sparse.eval nodeValue3802 (mixedVector B) := by
    change mixedMoment B node3802 node3802Labels = _
    exact sound3802 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847_e B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852_e B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3878 : mixedVector B (Sum.inr 3878) = Sparse.eval nodeValue3878 (mixedVector B) := by
    change mixedMoment B node3878 node3878Labels = _
    exact sound3878 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3938 : mixedVector B (Sum.inr 3938) = Sparse.eval nodeValue3938 (mixedVector B) := by
    change mixedMoment B node3938 node3938Labels = _
    exact sound3938_e B hB hF
  have h3976 : mixedVector B (Sum.inr 3976) = Sparse.eval nodeValue3976 (mixedVector B) := by
    change mixedMoment B node3976 node3976Labels = _
    exact sound3976 B hB hF
  have h3995 : mixedVector B (Sum.inr 3995) = Sparse.eval nodeValue3995 (mixedVector B) := by
    change mixedMoment B node3995 node3995Labels = _
    exact sound3995_e B hB hF
  simpa only [sourceForm954, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2606, h2607, h2631, h2676, h3524, h3525, h3527, h3566, h3780, h3799, h3800, h3802, h3847, h3850, h3852, h3854, h3878, h3881, h3938, h3976, h3995, reducedSource833] using sourceEq954 B hB

theorem rowSound833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row833 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck833, numericCheck833, reducedZero833 B hB hF, mul_zero]

theorem reducedZero835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource835 (mixedVector B) = 0 := by
  have h2878 : mixedVector B (Sum.inr 2878) = Sparse.eval nodeValue2878 (mixedVector B) := by
    change mixedMoment B node2878 node2878Labels = _
    exact sound2878 B hB hF
  have h3703 : mixedVector B (Sum.inr 3703) = Sparse.eval nodeValue3703 (mixedVector B) := by
    change mixedMoment B node3703 node3703Labels = _
    exact sound3703 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3956 : mixedVector B (Sum.inr 3956) = Sparse.eval nodeValue3956 (mixedVector B) := by
    change mixedMoment B node3956 node3956Labels = _
    exact sound3956 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm956, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2878, h3703, h3874, h3956, h3961, h4092, reducedSource835] using sourceEq956 B hB

theorem rowSound835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row835 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck835, numericCheck835, reducedZero835 B hB hF, mul_zero]

theorem reducedZero836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource836 (mixedVector B) = 0 := by
  have h2630 : mixedVector B (Sum.inr 2630) = Sparse.eval nodeValue2630 (mixedVector B) := by
    change mixedMoment B node2630 node2630Labels = _
    exact sound2630 B hB hF
  have h2869 : mixedVector B (Sum.inr 2869) = Sparse.eval nodeValue2869 (mixedVector B) := by
    change mixedMoment B node2869 node2869Labels = _
    exact sound2869 B hB hF
  have h3697 : mixedVector B (Sum.inr 3697) = Sparse.eval nodeValue3697 (mixedVector B) := by
    change mixedMoment B node3697 node3697Labels = _
    exact sound3697 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm957, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2630, h2869, h3697, h3874, h3884, h4092, reducedSource836] using sourceEq957 B hB

theorem rowSound836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row836 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck836, numericCheck836, reducedZero836 B hB hF, mul_zero]

theorem reducedZero837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource837 (mixedVector B) = 0 := by
  have h3786 : mixedVector B (Sum.inr 3786) = Sparse.eval nodeValue3786 (mixedVector B) := by
    change mixedMoment B node3786 node3786Labels = _
    exact sound3786 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3956 : mixedVector B (Sum.inr 3956) = Sparse.eval nodeValue3956 (mixedVector B) := by
    change mixedMoment B node3956 node3956Labels = _
    exact sound3956 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm958, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3786, h3788, h3805, h3874, h3956, h4092, reducedSource837] using sourceEq958 B hB

theorem rowSound837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row837 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck837, numericCheck837, reducedZero837 B hB hF, mul_zero]

theorem reducedZero838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource838 (mixedVector B) = 0 := by
  have h2869 : mixedVector B (Sum.inr 2869) = Sparse.eval nodeValue2869 (mixedVector B) := by
    change mixedMoment B node2869 node2869Labels = _
    exact sound2869 B hB hF
  have h2870 : mixedVector B (Sum.inr 2870) = Sparse.eval nodeValue2870 (mixedVector B) := by
    change mixedMoment B node2870 node2870Labels = _
    exact sound2870 B hB hF
  have h2878 : mixedVector B (Sum.inr 2878) = Sparse.eval nodeValue2878 (mixedVector B) := by
    change mixedMoment B node2878 node2878Labels = _
    exact sound2878 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm959, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2869, h2870, h2878, h3043, h3874, h4092, reducedSource838] using sourceEq959 B hB

theorem rowSound838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row838 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck838, numericCheck838, reducedZero838 B hB hF, mul_zero]

theorem reducedZero839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource839 (mixedVector B) = 0 := by
  have h2614 : mixedVector B (Sum.inr 2614) = Sparse.eval nodeValue2614 (mixedVector B) := by
    change mixedMoment B node2614 node2614Labels = _
    exact sound2614 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3786 : mixedVector B (Sum.inr 3786) = Sparse.eval nodeValue3786 (mixedVector B) := by
    change mixedMoment B node3786 node3786Labels = _
    exact sound3786 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm960, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2614, h3043, h3786, h3850, h3874, h4092, reducedSource839] using sourceEq960 B hB

theorem rowSound839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row839 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck839, numericCheck839, reducedZero839 B hB hF, mul_zero]

theorem reducedZero843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource843 (mixedVector B) = 0 := by
  have h5085 : mixedVector B (Sum.inr 5085) = Sparse.eval nodeValue5085 (mixedVector B) := by
    change mixedMoment B node5085 node5085Labels = _
    exact sound5085 B hB hF
  have h5086 : mixedVector B (Sum.inr 5086) = Sparse.eval nodeValue5086 (mixedVector B) := by
    change mixedMoment B node5086 node5086Labels = _
    exact sound5086 B hB hF
  have h5098 : mixedVector B (Sum.inr 5098) = Sparse.eval nodeValue5098 (mixedVector B) := by
    change mixedMoment B node5098 node5098Labels = _
    exact sound5098 B hB hF
  have h5254 : mixedVector B (Sum.inr 5254) = Sparse.eval nodeValue5254 (mixedVector B) := by
    change mixedMoment B node5254 node5254Labels = _
    exact sound5254 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5286 : mixedVector B (Sum.inr 5286) = Sparse.eval nodeValue5286 (mixedVector B) := by
    change mixedMoment B node5286 node5286Labels = _
    exact sound5286 B hB hF
  have h5359 : mixedVector B (Sum.inr 5359) = Sparse.eval nodeValue5359 (mixedVector B) := by
    change mixedMoment B node5359 node5359Labels = _
    exact sound5359 B hB hF
  have h5360 : mixedVector B (Sum.inr 5360) = Sparse.eval nodeValue5360 (mixedVector B) := by
    change mixedMoment B node5360 node5360Labels = _
    exact sound5360 B hB hF
  have h5365 : mixedVector B (Sum.inr 5365) = Sparse.eval nodeValue5365 (mixedVector B) := by
    change mixedMoment B node5365 node5365Labels = _
    exact sound5365 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5407 : mixedVector B (Sum.inr 5407) = Sparse.eval nodeValue5407 (mixedVector B) := by
    change mixedMoment B node5407 node5407Labels = _
    exact sound5407 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  simpa only [sourceForm966, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5085, h5086, h5098, h5254, h5256, h5265, h5286, h5359, h5360, h5365, h5405, h5406, h5407, h5410, h5411, h5412, h5429, h5434, h5435, reducedSource843] using sourceEq966 B hB

theorem rowSound843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row843 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck843, numericCheck843, reducedZero843 B hB hF, mul_zero]

theorem reducedZero845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource845 (mixedVector B) = 0 := by
  have h3016 : mixedVector B (Sum.inr 3016) = Sparse.eval nodeValue3016 (mixedVector B) := by
    change mixedMoment B node3016 node3016Labels = _
    exact sound3016 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h3461 : mixedVector B (Sum.inr 3461) = Sparse.eval nodeValue3461 (mixedVector B) := by
    change mixedMoment B node3461 node3461Labels = _
    exact sound3461 B hB hF
  have h3464 : mixedVector B (Sum.inr 3464) = Sparse.eval nodeValue3464 (mixedVector B) := by
    change mixedMoment B node3464 node3464Labels = _
    exact sound3464 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3759 : mixedVector B (Sum.inr 3759) = Sparse.eval nodeValue3759 (mixedVector B) := by
    change mixedMoment B node3759 node3759Labels = _
    exact sound3759 B hB hF
  have h3762 : mixedVector B (Sum.inr 3762) = Sparse.eval nodeValue3762 (mixedVector B) := by
    change mixedMoment B node3762 node3762Labels = _
    exact sound3762 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847_e B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853_e B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3977 : mixedVector B (Sum.inr 3977) = Sparse.eval nodeValue3977 (mixedVector B) := by
    change mixedMoment B node3977 node3977Labels = _
    exact sound3977_e B hB hF
  have h3982 : mixedVector B (Sum.inr 3982) = Sparse.eval nodeValue3982 (mixedVector B) := by
    change mixedMoment B node3982 node3982Labels = _
    exact sound3982_e B hB hF
  simpa only [sourceForm968, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3016, h3023, h3037, h3085, h3460, h3461, h3464, h3526, h3758, h3759, h3762, h3800, h3803, h3808, h3809, h3814, h3847, h3853, h3954, h3977, h3982, reducedSource845] using sourceEq968 B hB

theorem rowSound845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row845 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck845, numericCheck845, reducedZero845 B hB hF, mul_zero]

theorem reducedZero846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource846 (mixedVector B) = 0 := by
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h3703 : mixedVector B (Sum.inr 3703) = Sparse.eval nodeValue3703 (mixedVector B) := by
    change mixedMoment B node3703 node3703Labels = _
    exact sound3703 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm969, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2508, h3703, h3805, h3812, h3816, h4092, reducedSource846] using sourceEq969 B hB

theorem rowSound846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row846 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck846, numericCheck846, reducedZero846 B hB hF, mul_zero]

theorem sourceRowsAt832 : MixedData.sourceRows (832 : Fin 2425) =
    MixedData.row832 := by decide +kernel

theorem sourceRowsAt833 : MixedData.sourceRows (833 : Fin 2425) =
    MixedData.row833 := by decide +kernel

theorem sourceRowsAt834 : MixedData.sourceRows (834 : Fin 2425) =
    MixedData.row834 := by decide +kernel

theorem sourceRowsAt835 : MixedData.sourceRows (835 : Fin 2425) =
    MixedData.row835 := by decide +kernel

theorem sourceRowsAt836 : MixedData.sourceRows (836 : Fin 2425) =
    MixedData.row836 := by decide +kernel

theorem sourceRowsAt837 : MixedData.sourceRows (837 : Fin 2425) =
    MixedData.row837 := by decide +kernel

theorem sourceRowsAt838 : MixedData.sourceRows (838 : Fin 2425) =
    MixedData.row838 := by decide +kernel

theorem sourceRowsAt839 : MixedData.sourceRows (839 : Fin 2425) =
    MixedData.row839 := by decide +kernel

theorem sourceRowsAt840 : MixedData.sourceRows (840 : Fin 2425) =
    MixedData.row840 := by decide +kernel

theorem sourceRowsAt841 : MixedData.sourceRows (841 : Fin 2425) =
    MixedData.row841 := by decide +kernel

theorem sourceRowsAt842 : MixedData.sourceRows (842 : Fin 2425) =
    MixedData.row842 := by decide +kernel

theorem sourceRowsAt843 : MixedData.sourceRows (843 : Fin 2425) =
    MixedData.row843 := by decide +kernel

theorem sourceRowsAt844 : MixedData.sourceRows (844 : Fin 2425) =
    MixedData.row844 := by decide +kernel

theorem sourceRowsAt845 : MixedData.sourceRows (845 : Fin 2425) =
    MixedData.row845 := by decide +kernel

theorem sourceRowsAt846 : MixedData.sourceRows (846 : Fin 2425) =
    MixedData.row846 := by decide +kernel

theorem sourceRowsAt847 : MixedData.sourceRows (847 : Fin 2425) =
    MixedData.row847 := by decide +kernel

theorem chunkSound52_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 52) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 832 ∨ k.val = 833 ∨ k.val = 834 ∨ k.val = 835 ∨ k.val = 836 ∨ k.val = 837 ∨ k.val = 838 ∨ k.val = 839 ∨ k.val = 840 ∨ k.val = 841 ∨ k.val = 842 ∨ k.val = 843 ∨ k.val = 844 ∨ k.val = 845 ∨ k.val = 846 ∨ k.val = 847 := by omega
  rcases heq with h832 | h833 | h834 | h835 | h836 | h837 | h838 | h839 | h840 | h841 | h842 | h843 | h844 | h845 | h846 | h847
  · have he : k = (832 : Fin 2425) := Fin.ext h832
    subst k
    rw [sourceRowsAt832]
    exact rowSound832 B hB hF
  · have he : k = (833 : Fin 2425) := Fin.ext h833
    subst k
    rw [sourceRowsAt833]
    exact rowSound833 B hB hF
  · have he : k = (834 : Fin 2425) := Fin.ext h834
    subst k
    rw [sourceRowsAt834]
    exact rowSound834_e B hB hF
  · have he : k = (835 : Fin 2425) := Fin.ext h835
    subst k
    rw [sourceRowsAt835]
    exact rowSound835 B hB hF
  · have he : k = (836 : Fin 2425) := Fin.ext h836
    subst k
    rw [sourceRowsAt836]
    exact rowSound836 B hB hF
  · have he : k = (837 : Fin 2425) := Fin.ext h837
    subst k
    rw [sourceRowsAt837]
    exact rowSound837 B hB hF
  · have he : k = (838 : Fin 2425) := Fin.ext h838
    subst k
    rw [sourceRowsAt838]
    exact rowSound838 B hB hF
  · have he : k = (839 : Fin 2425) := Fin.ext h839
    subst k
    rw [sourceRowsAt839]
    exact rowSound839 B hB hF
  · have he : k = (840 : Fin 2425) := Fin.ext h840
    subst k
    rw [sourceRowsAt840]
    exact rowSound840_e B hB hF
  · have he : k = (841 : Fin 2425) := Fin.ext h841
    subst k
    rw [sourceRowsAt841]
    exact rowSound841_e B hB hF
  · have he : k = (842 : Fin 2425) := Fin.ext h842
    subst k
    rw [sourceRowsAt842]
    exact rowSound842_e B hB hF
  · have he : k = (843 : Fin 2425) := Fin.ext h843
    subst k
    rw [sourceRowsAt843]
    exact rowSound843 B hB hF
  · have he : k = (844 : Fin 2425) := Fin.ext h844
    subst k
    rw [sourceRowsAt844]
    exact rowSound844_e B hB hF
  · have he : k = (845 : Fin 2425) := Fin.ext h845
    subst k
    rw [sourceRowsAt845]
    exact rowSound845 B hB hF
  · have he : k = (846 : Fin 2425) := Fin.ext h846
    subst k
    rw [sourceRowsAt846]
    exact rowSound846 B hB hF
  · have he : k = (847 : Fin 2425) := Fin.ext h847
    subst k
    rw [sourceRowsAt847]
    exact rowSound847_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e_oai
