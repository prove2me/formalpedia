-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_tilted_scale_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:19:36.946471+00:00
-- url     : https://prove2.me/submissions/e880ee44-a156-46ae-b958-029e3a6cd900
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_source_scale_cumulative
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_potential_total_mass
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_derivative_exact
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    Monotone (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) ∧ Tendsto (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) atTop (𝓝 (deriv (Phi ψ) q)) := by
  obtain ⟨ν, hs, hf, hlap, he⟩ := p2m89_source_scale_cumulative D ψ W hψ hW q hq
  have hmass := p2m89_potential_total_mass D ψ W hψ hW q hq ν hs hlap
  obtain ⟨hp, hd⟩ := p2m89_phi_derivative_exact D ψ W hψ hW q hq
  have hnonneg : 0 ≤ deriv (Phi ψ) q := by rw [hd]; positivity
  have hlim := (ENNReal.tendsto_toReal (a := ν univ)
    (by rw [hmass]; exact ENNReal.ofReal_ne_top)).comp (tendsto_measure_Iic_atTop ν)
  rw [hmass, ENNReal.toReal_ofReal hnonneg] at hlim
  refine ⟨?_, ?_⟩
  · intro r s hrs
    calc
      Real.exp (-Phi ψ q * r) * W q r = (ν (Iic r)).toReal := he r
      _ ≤ (ν (Iic s)).toReal :=
        ENNReal.toReal_mono (hf s).ne (measure_mono (Iic_subset_Iic.mpr hrs))
      _ = Real.exp (-Phi ψ q * s) * W q s := (he s).symm
  · exact hlim.congr' (Eventually.of_forall fun r => (he r).symm)
