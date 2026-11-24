-- Prove2me | solution 1 for Kyprianou.Ch03.stableLevyMomentRightFatouV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:58.145901+00:00
-- url     : https://prove2.me/submissions/b24533ff-96a8-4bd8-9f4c-6bb1480ec9e2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (θ : ℝ) (s : ℝ≥0) (sn : ℕ → ℝ≥0)
    (hge : ∀ n, s ≤ sn n) (ht : Tendsto sn atTop (nhds s)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (sn n) ω)) ∂P) atTop := by
  have hm (t : NNReal) : AEMeasurable (X t) P := by
    have hi := (hX.stationary_increments 0 t).aemeasurable_snd
    change AEMeasurable (fun w => X t w - X 0 w) P at hi
    simpa only [hX.start_zero, sub_zero] using hi
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (θ * z))
  have hreal : Continuous (fun z : ℝ => Real.exp (θ * z)) := by fun_prop
  have hc : Continuous f := ENNReal.continuous_ofReal.comp hreal
  have hwithin : Tendsto sn atTop (nhdsWithin s (Ici s)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, Eventually.of_forall hge⟩
  have hlim : (fun ω => Filter.liminf (fun n => f (X (sn n) ω)) atTop)
      =ᵐ[P] fun ω => f (X s ω) := by
    filter_upwards [hX.cadlag_ae] with ω hcad
    exact ((hc.tendsto _).comp (((hcad s).1).tendsto.comp hwithin)).liminf_eq
  calc
    (∫⁻ ω, f (X s ω) ∂P) =
        ∫⁻ ω, Filter.liminf (fun n => f (X (sn n) ω)) atTop ∂P :=
      lintegral_congr_ae hlim.symm
    _ ≤ _ := lintegral_liminf_le' (fun n =>
      hc.measurable.comp_aemeasurable (hm (sn n)))
