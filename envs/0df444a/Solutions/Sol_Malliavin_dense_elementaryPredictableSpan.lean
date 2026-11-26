-- Prove2me | solution 1 for Malliavin.dense_elementaryPredictableSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:28.837666+00:00
-- url     : https://prove2.me/submissions/9c746d29-1fcf-4792-a676-eaad861fc984

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
import Theorems.Thm_Malliavin_ae_eq_zero_of_orthogonal_elementaryPredictable

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W)) :
    Dense (elementaryPredictableSpan (P := P) 𝓕 :
      Set (PredictableProcessL2 𝓕 P)) := by
  let _ : Fact (𝓕.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × W))) := ⟨predictable_le_prod 𝓕⟩
  suffices horthbot : (elementaryPredictableSpan (P := P) 𝓕)ᗮ = ⊥ by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      Submodule.topologicalClosure_eq_top_iff.mpr horthbot, Submodule.top_coe]
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  apply Subtype.ext
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr
    (ae_eq_zero_of_orthogonal_elementaryPredictable 𝓕 g
      (fun U hU ↦ hg U hU))
end Malliavin
