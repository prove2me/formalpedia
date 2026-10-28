-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.stageCoefficient_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:48:44.791964+00:00
-- url     : https://prove2.me/submissions/7bc1d41f-0cb6-45b7-9fea-164428d039d7

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_MatrixModule_endpoint_unit_bound

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

lemma norm_center_le (Ω x : E) : ‖center Ω x‖ ≤ ‖x‖ :=
  (centeredSpace Ω).norm_orthogonalProjectionOnto_apply_le x

end Kadison
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

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointModule2
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

namespace Kadison

variable {I : Type*} [Fintype I] [DecidableEq I]

namespace MatrixModule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable (ρ : Matrix I I ℂ →⋆ₐ[ℂ] (E →L[ℂ] E)) (Ω : E)
  (htrace : ∀ a, inner ℂ Ω (ρ a Ω) = normalizedTrace a)

include htrace in
lemma inner_vector (a b : Matrix I I ℂ) :
    inner ℂ (ρ a Ω) (ρ b Ω) = normalizedTrace (star a * b) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ Ω (star (ρ a) (ρ b Ω)) = _
  rw [← map_star]
  change inner ℂ Ω ((ρ (star a) * ρ b) Ω) = _
  rw [← map_mul, htrace]

include htrace in
lemma norm_vector_single (i j : I) :
    ‖ρ (Matrix.single i j 1) Ω‖ = Real.sqrt (Fintype.card I : ℝ)⁻¹ := by
  have hs : ‖ρ (Matrix.single i j 1) Ω‖ ^ 2 = (Fintype.card I : ℝ)⁻¹ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_vector ρ Ω htrace]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
      star_one, Matrix.single_mul_single_same, normalizedTrace,
      Matrix.trace_single_eq_same, mul_one]
    change ((Fintype.card I : ℂ)⁻¹).re = _
    rw [Complex.inv_re]
    simp
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

end MatrixModule

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointGNS2
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

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

include hτ h1 in
lemma stageRepresentation_trace (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (a : Matrix I I ℂ) :
    inner ℂ (vacuum τ) (stageRepresentation τ φ a (vacuum τ)) = normalizedTrace a := by
  rw [stageRepresentation_vacuum]
  change inner ℂ (vacuum τ) (algebraVector τ (φ a)) = _
  rw [inner_vacuum_algebraVector, stage_trace τ hτ h1 φ]
  rfl

include hτ h1 in
lemma norm_centeredStageVector_single (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (i j : I) :
    ‖centeredStageVector τ φ (Matrix.single i j 1)‖ ≤ Real.sqrt (Fintype.card I : ℝ)⁻¹ := by
  calc
    _ ≤ ‖stageVector τ φ (Matrix.single i j 1)‖ :=
      norm_center_le (vacuum τ) _
    _ = _ := by
      rw [← stageRepresentation_vacuum]
      exact MatrixModule.norm_vector_single (stageRepresentation τ φ) (vacuum τ)
        (stageRepresentation_trace τ hτ h1 φ) i j

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

include hτ h1 in
lemma stageCoefficient_rank_one_oai (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (hY : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y)
    (b : Option (Fin k ⊕ Fin l) → I)
    (σ : Equiv.Perm (Option (Fin k ⊕ Fin l))) :
    ‖stageCoefficient τ Y φ (fun j => Matrix.single (b (σ j)) (b j) 1)‖ ≤
      ‖Y‖ * (Fintype.card I : ℝ)⁻¹ *
        (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ (Fintype.card (Option (Fin k ⊕ Fin l)) - 1) := by
  let v : Option (Fin k ⊕ Fin l) → Matrix I I ℂ :=
    fun j => Matrix.single (b (σ j)) (b j) 1
  have hleft (a : Matrix I I ℂ) :
      Y.comp (HilbertTensor.map (stageRepresentation τ φ a)
        (1 : power (zeroSpace τ) k →L[ℂ] power (zeroSpace τ) k)) =
      (HilbertTensor.map (stageRepresentation τ φ a)
        (1 : power (zeroSpace τ) l →L[ℂ] power (zeroSpace τ) l)).comp Y := hY (φ a)
  have h := MatrixModule.endpoint_unit_bound (stageRepresentation τ φ) (vacuum τ)
    (stageRepresentation_trace τ hτ h1 φ) Y hleft (b none) (b (σ none))
    (pure (zeroSpace τ) k (fun i => centeredStageVector τ φ (v (some (.inl i)))))
    (pure (zeroSpace τ) l (fun i => centeredStageVector τ φ (star (v (some (.inr i))))))
  have hs (j) : star (v j) = Matrix.single (b j) (b (σ j)) 1 := by
    simp only [v, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]
  have hcoeff : ‖stageCoefficient τ Y φ v‖ ≤
      ‖Y‖ * (Fintype.card I : ℝ)⁻¹ *
        ‖pure (zeroSpace τ) k (fun i => centeredStageVector τ φ (v (some (.inl i))))‖ *
        ‖pure (zeroSpace τ) l (fun i => centeredStageVector τ φ (star (v (some (.inr i)))))‖ := by
    change ‖coefficient (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
      (stageVector τ φ) (centeredStageVector τ φ) v‖ ≤ _
    simpa only [coefficient, word, hs, stageRepresentation_vacuum] using h
  have hx : ‖pure (zeroSpace τ) k (fun i => centeredStageVector τ φ (v (some (.inl i))))‖ ≤
      (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ k := by
    rw [norm_pure]
    calc
      _ ≤ ∏ _ : Fin k, Real.sqrt (Fintype.card I : ℝ)⁻¹ :=
        Finset.prod_le_prod (by intros; positivity) (fun i _ => norm_centeredStageVector_single τ hτ h1 φ _ _)
      _ = _ := by simp
  have hz : ‖pure (zeroSpace τ) l (fun i => centeredStageVector τ φ (star (v (some (.inr i)))))‖ ≤
      (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ l := by
    rw [norm_pure]
    calc
      _ ≤ ∏ _ : Fin l, Real.sqrt (Fintype.card I : ℝ)⁻¹ :=
        Finset.prod_le_prod (by intros; positivity) (fun i _ => by
          rw [hs]; exact norm_centeredStageVector_single τ hτ h1 φ _ _)
      _ = _ := by simp
  calc
    _ ≤ _ := hcoeff
    _ ≤ ‖Y‖ * (Fintype.card I : ℝ)⁻¹ *
        (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ k * (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ l := by
      gcongr
    _ = _ := by simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin,
      Nat.add_sub_cancel_right, pow_add]; ring

end Kadison.TracialGNS
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TracialGNS.stageCoefficient_rank_one_oai.{u_1} := @OAI.Kadison.TracialGNS.stageCoefficient_rank_one_oai.{u_1}
