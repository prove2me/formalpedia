-- Prove2me | solution 1 for GlobalTheory.HaarScaleMatrix.integral_comp_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:19.970799+00:00
-- url     : https://prove2.me/submissions/94a424b3-a049-4f1b-8619-562d7ee05b66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRk
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureAdditiveAutomorphismScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory
open GlobalTheory GlobalTheory.HaarScaleMatrix
namespace GlobalTheory.HaarScaleMatrix
theorem _root_.solution {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (L : G ≃+ G) (hL : Continuous L) (hL' : Continuous L.symm) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ℂ, ∫ x, f (L x) ∂μ = (c : ℂ) * ∫ x, f x ∂μ := by
  haveI : (μ.map L).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ L hL hL'
  let H : G ≃ₜ G := { toEquiv := L.toEquiv, continuous_toFun := hL, continuous_invFun := hL' }
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map L) μ
  refine ⟨(Measure.addHaarScalarFactor (μ.map L) μ : ℝ), ?_, fun f => ?_⟩
  · exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map L) μ
  · have h1 : ∫ x, f x ∂(μ.map L) = ∫ x, f (L x) ∂μ :=
      integral_map_equiv H.toMeasurableEquiv f
    rw [← h1]
    conv_lhs => rw [hs]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
end GlobalTheory.HaarScaleMatrix
