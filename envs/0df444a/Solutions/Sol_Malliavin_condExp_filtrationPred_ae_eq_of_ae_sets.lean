-- Prove2me | solution 1 for Malliavin.condExp_filtrationPred_ae_eq_of_ae_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:34.352407+00:00
-- url     : https://prove2.me/submissions/b7cf3abe-a00a-4995-b4b0-6df9d1e4bdc1

import Definitions.Def_Malliavin_PointwiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Theorems.Thm_Malliavin_filtrationPred_le


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (hcomplete : ∀ s : Set W, MeasurableSet[𝓕 t] s →
      ∃ r : Set W, MeasurableSet[filtrationPred 𝓕 t] r ∧ s =ᵐ[P] r)
    (X : W → ℝ) (hX : Integrable X P) :
    P[X | filtrationPred 𝓕 t] =ᵐ[P] P[X | 𝓕 t] := by
  let Y : W → ℝ := P[X | filtrationPred 𝓕 t]
  have hpredt : filtrationPred 𝓕 t ≤ 𝓕 t :=
    iSup₂_le fun u (hut : u < t) ↦ 𝓕.mono hut.le
  apply ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t) hX
  · intro s _ _
    exact integrable_condExp.integrableOn
  · intro s hs _
    obtain ⟨r, hr, hsr⟩ := hcomplete s hs
    calc
      ∫ x in s, Y x ∂P = ∫ x in r, Y x ∂P := setIntegral_congr_set hsr
      _ = ∫ x in r, X x ∂P := setIntegral_condExp (filtrationPred_le 𝓕 t) hX hr
      _ = ∫ x in s, X x ∂P := (setIntegral_congr_set hsr).symm
  · exact (stronglyMeasurable_condExp.mono hpredt).aestronglyMeasurable
end Malliavin
