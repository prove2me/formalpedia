-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.normalizedLetter_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:28:45.278142+00:00
-- url     : https://prove2.me/submissions/3bb78950-8d33-45c2-8672-05108749a5f8

import Mathlib
import Definitions.Def_OAIQ039C052

section
-- module Solutions.OAIQ039_CM.Commutator_CenteredSpace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma coe_center (Ω : E) (hΩ : ‖Ω‖ = 1) (x : E) :
    (center Ω x : E) = x - inner ℂ Ω x • Ω := by
  change (ℂ ∙ Ω)ᗮ.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℂ hΩ]

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HermitianAlphabet
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.MatrixAlphabet

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma trace_letter (o i : I) (hi : i ≠ o) : (letter o i).trace = 0 := by
  simp [letter, Matrix.trace_single_eq_of_ne _ _ _ hi, Matrix.trace_single_eq_of_ne _ _ _ hi.symm]

lemma trace_mul_letter (o i j : I) (hi : i ≠ o) (hj : j ≠ o) :
    (letter o i * letter o j).trace = if i = j then 2 else 0 := by
  classical
  simp only [letter, add_mul, mul_add, Matrix.trace_add]
  rw [Matrix.single_mul_single_of_ne (1 : ℂ) o i o hi 1,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (1 : ℂ) i o j hj.symm 1]
  simp only [Matrix.trace_zero, zero_add, one_mul]
  by_cases h : i = j
  · subst j
    norm_num
  · rw [Matrix.single_mul_single_of_ne (1 : ℂ) o i j h 1]
    simp [h, Matrix.trace_single_eq_of_ne _ _ _ h]

omit [DecidableEq I] in
lemma scale_sq : (scale (I := I)) ^ 2 = (Fintype.card I : ℂ) / 2 := by
  rw [scale, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  push_cast
  rfl

lemma trace_normalizedLetter (o i : I) (hi : i ≠ o) : (normalizedLetter o i).trace = 0 := by
  simp only [normalizedLetter, Matrix.trace_smul, trace_letter o i hi, smul_zero]

lemma normalized_trace_mul [Nonempty I] (o i j : I) (hi : i ≠ o) (hj : j ≠ o) :
    (Fintype.card I : ℂ)⁻¹ * (normalizedLetter o i * normalizedLetter o j).trace =
      if i = j then 1 else 0 := by
  have hm : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [normalizedLetter, normalizedLetter, smul_mul_smul_comm, Matrix.trace_smul,
    trace_mul_letter o i j hi hj]
  simp only [smul_eq_mul, ← sq, scale_sq]
  split_ifs <;> field_simp
  norm_num

end Kadison.MatrixAlphabet
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.MatrixTrace

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →ₗ[ℂ] ℂ)

variable (htr : ∀ x y, φ (x * y) = φ (y * x)) (hunit : φ 1 = 1)

include htr

lemma off_diagonal (i j : I) (hij : i ≠ j) : φ (single i j 1) = 0 := by
  have h := htr (single i i 1) (single i j 1)
  have hz : (single i j (1 : ℂ)) * single i i 1 = 0 :=
    Matrix.single_mul_single_of_ne 1 i j i hij.symm 1
  simpa [hz] using h

lemma diagonal_eq (i j : I) : φ (single i i 1) = φ (single j j 1) := by
  simpa using htr (single i j 1) (single j i 1)

variable [Nonempty I]

include hunit

lemma diagonal (i : I) : φ (single i i 1) = (Fintype.card I : ℂ)⁻¹ := by
  have hcard : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h : (Fintype.card I : ℂ) * φ (single i i 1) = 1 := by
    calc
      _ = ∑ j : I, φ (single j j 1) := by
        simp only [← diagonal_eq φ htr i, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      _ = φ 1 := by rw [← map_sum, Matrix.sum_single_one]
      _ = 1 := hunit
  apply (mul_left_cancel₀ hcard)
  rw [h, mul_inv_cancel₀ hcard]

lemma unique (a : Matrix I I ℂ) : φ a = (Fintype.card I : ℂ)⁻¹ * a.trace := by
  have hsingle (i j : I) : φ (single i j (a i j)) =
      if i = j then (Fintype.card I : ℂ)⁻¹ * a i j else 0 := by
    have hs : single i j (a i j) = a i j • (single i j (1 : ℂ)) := by
      ext k l
      simp [Matrix.single]
    rw [hs, map_smul]
    by_cases hij : i = j
    · subst j
      rw [diagonal φ htr hunit, ite_eq_left rfl]
      exact mul_comm _ _
    · rw [off_diagonal φ htr i j hij, ite_eq_right hij, smul_zero]
  calc
    φ a = ∑ i : I, ∑ j : I, φ (single i j (a i j)) := by
      nth_rw 1 [Matrix.matrix_eq_sum_single a]
      simp only [map_sum]
    _ = (Fintype.card I : ℂ)⁻¹ * a.trace := by
      simp [hsingle, Matrix.trace, ← Finset.mul_sum]

end Kadison.MatrixTrace
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

omit [StarOrderedRing A] in
include hτ h1 in
lemma stage_trace (a : Matrix I I ℂ) :
    τ (φ a) = (Fintype.card I : ℂ)⁻¹ * a.trace := by
  apply MatrixTrace.unique (τ.toLinearMap.comp φ.toLinearMap)
  · intro x y
    change τ (φ (x*y)) = τ (φ (y*x))
    simpa only [map_mul] using hτ (φ x) (φ y)
  · change τ (φ 1) = 1
    simpa using h1

include hτ h1 in
lemma stage_inner (a b : Matrix I I ℂ) :
    inner ℂ (stageVector τ φ a) (stageVector τ φ b) =
      (Fintype.card I : ℂ)⁻¹ * (star a * b).trace := by
  change inner ℂ (algebraVector τ (φ a)) (algebraVector τ (φ b)) = _
  rw [inner_algebraVector, ← map_star, ← map_mul, stage_trace τ hτ h1 φ]

include hτ h1 in
lemma stage_centered (a : Matrix I I ℂ) :
    (centeredStageVector τ φ a : τ.GNS) =
      stageVector τ φ a - ((Fintype.card I : ℂ)⁻¹ * a.trace) • vacuum τ := by
  change (center (vacuum τ) (algebraVector τ (φ a)) : τ.GNS) = _
  rw [coe_center _ (vacuum_norm τ h1), inner_vacuum_algebraVector,
    stage_trace τ hτ h1 φ]
  rfl

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HermitianAlphabet2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open MatrixAlphabet

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

include hτ h1 in
lemma centered_normalizedLetter (o i : I) (hi : i ≠ o) :
    (centeredStageVector τ φ (normalizedLetter o i) : τ.GNS) =
      stageVector τ φ (normalizedLetter o i) := by
  rw [stage_centered τ hτ h1, trace_normalizedLetter o i hi, mul_zero, zero_smul, sub_zero]

include hτ h1 in
lemma normalizedLetter_orthonormal_oai {J : Type*} (o : I) (b : J ↪ I)
    (hb : ∀ j, b j ≠ o) :
    Orthonormal ℂ (fun j => centeredStageVector τ φ (normalizedLetter o (b j))) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℂ (centeredStageVector τ φ (normalizedLetter o (b i)) : τ.GNS)
    (centeredStageVector τ φ (normalizedLetter o (b j)) : τ.GNS) = _
  rw [centered_normalizedLetter τ hτ h1 φ o _ (hb i),
    centered_normalizedLetter τ hτ h1 φ o _ (hb j), stage_inner τ hτ h1,
    star_normalizedLetter, normalized_trace_mul o _ _ (hb i) (hb j)]
  simp only [EmbeddingLike.apply_eq_iff_eq]

end Kadison.TracialGNS
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.TracialGNS.normalizedLetter_orthonormal_oai.{u_1, u_2, u_3} := @OAI.Kadison.TracialGNS.normalizedLetter_orthonormal_oai.{u_1, u_2, u_3}
