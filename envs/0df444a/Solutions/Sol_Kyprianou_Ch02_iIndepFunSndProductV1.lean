-- Prove2me | solution 1 for Kyprianou.Ch02.iIndepFunSndProductV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:40:59.556319+00:00
-- url     : https://prove2.me/submissions/95532349-c228-4a89-843f-d240361e0ad6

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib.Probability.Independence.Basic
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

set_option autoImplicit false

theorem solution
    {Ω₁ Ω₂ ι : Type*} {β : ι → Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [(i : ι) → MeasurableSpace (β i)]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {f : (i : ι) → Ω₂ → β i} (hf : iIndepFun f P₂) :
    iIndepFun (fun i (ω : Ω₁ × Ω₂) => f i ω.2) (P₁.prod P₂) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hsets
  have hprod : (⋂ i ∈ S, (fun ω : Ω₁ × Ω₂ => f i ω.2) ⁻¹' sets i) =
      (Set.univ : Set Ω₁) ×ˢ (⋂ i ∈ S, f i ⁻¹' sets i) := by
    ext ⟨a, b⟩; simp
  have hsingle : ∀ i, (fun ω : Ω₁ × Ω₂ => f i ω.2) ⁻¹' sets i =
      (Set.univ : Set Ω₁) ×ˢ (f i ⁻¹' sets i) := fun _ => by
    ext ⟨a, b⟩; simp
  rw [hprod, Measure.prod_prod, measure_univ, one_mul, hf S hsets]
  congr 1; funext i
  rw [hsingle i, Measure.prod_prod, measure_univ, one_mul]
