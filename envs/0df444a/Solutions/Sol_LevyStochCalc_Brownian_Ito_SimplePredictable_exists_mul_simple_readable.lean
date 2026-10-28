-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:01.675846+00:00
-- url     : https://prove2.me/submissions/1a888cec-d32a-4f50-aa8d-e705430095ba

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_appendInterval_integralAgainst_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_eval_mul_on_common_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_sum_xi_mul_simpleIntegral_sub_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- Adaptedness passes to the product on the common refinement. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.mul_on_common_adapt
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∀ j : Fin (H₁.mul_on_common H₂ h_eq).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((H₁.mul_on_common H₂ h_eq).partition j.castSucc))
        ((H₁.mul_on_common H₂ h_eq).ξ j) := by
  intro j
  have h₁ := (h_adapt₁ (H₁.mergedIdxMap_left H₂ h_eq j)).mono
    (ℱ.mono (H₁.mergedIdxMap_left_idx_le H₂ h_eq j))
  have h₂ := (h_adapt₂ (H₁.mergedIdxMap_right H₂ h_eq j)).mono
    (ℱ.mono (H₁.mergedIdxMap_right_idx_le H₂ h_eq j))
  exact h₁.mul h₂
/-- **The product of two simple integrands as a simple integrand.** For adapted `G` and `K` with
arbitrary horizons there is an adapted simple integrand `Q` whose evaluation is the product of
the evaluations and whose elementary integral is the elementary integral of `G` against the
elementary integral of `K`. -/
theorem solution
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T₁ T₂ : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₁) (K : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₂)
    (h_adaptG : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    (h_adaptK : ∀ i : Fin K.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (K.partition i.castSucc)) (K.ξ i)) :
    ∃ (T₃ : ℝ) (Q : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = G.eval s ω * K.eval s ω)
      ∧ (∀ t ω, G.integralAgainst (fun u ω' => LevyStochCalc.Brownian.Ito.simpleIntegral W K u ω') t ω
          = LevyStochCalc.Brownian.Ito.simpleIntegral W Q t ω) := by
  have hG : G.partition (Fin.last G.N)
      < max (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)) + 1 := by
    have := le_max_left (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)); linarith
  have hK : K.partition (Fin.last K.N)
      < max (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)) + 1 := by
    have := le_max_right (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)); linarith
  have h_eq : (G.appendInterval hG).partition (Fin.last (G.appendInterval hG).N)
      = (K.appendInterval hK).partition (Fin.last (K.appendInterval hK).N) :=
    (G.appendInterval_partition_last hG).trans (K.appendInterval_partition_last hK).symm
  refine ⟨_, (G.appendInterval hG).mul_on_common (K.appendInterval hK) h_eq, ?_, ?_, ?_⟩
  · exact LevyStochCalc.Brownian.Ito.SimplePredictable.mul_on_common_adapt ℱ _ _ h_eq
      (G.appendInterval_adapt ℱ hG h_adaptG) (K.appendInterval_adapt ℱ hK h_adaptK)
  · intro s ω
    rw [LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common_readable, G.appendInterval_eval hG,
      K.appendInterval_eval hK]
  · intro t ω
    rw [← LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub_readable W (G.appendInterval hG)
      (K.appendInterval hK) h_eq t ω]
    have hKfun : (fun u (ω' : Ω) => LevyStochCalc.Brownian.Ito.simpleIntegral W K u ω')
        = fun u ω' => LevyStochCalc.Brownian.Ito.simpleIntegral W (K.appendInterval hK) u ω' := by
      funext u ω'; exact (K.appendInterval_simpleIntegral W hK u ω').symm
    rw [hKfun, ← G.appendInterval_integralAgainst_readable hG
      (fun u ω' => LevyStochCalc.Brownian.Ito.simpleIntegral W (K.appendInterval hK) u ω') t ω]
    rfl
