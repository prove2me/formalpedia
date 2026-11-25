-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSection.awayImageS_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:07:41.041323+00:00
-- url     : https://prove2.me/submissions/27cbebba-e29a-401c-9769-824c9045fcf4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_FiniteIdeleDecomp
import Theorems.Thm_GroundTheory_Automorphic_GodementSection_measurable_finUnitsAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology GroundTheory.Global GroundTheory.LocalField
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {S}
namespace GroundTheory.Automorphic.GodementSection
theorem _root_.solution (g : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)
    {A : Set ((v : S) → (v.1.adicCompletion K)ˣ)} (hA : MeasurableSet A) :
    awayImageS S g A = ∫⁻ b, (finUnitsAt S ⁻¹' A).indicator g b ∂finiteIdeleMeasure K := by
  rw [awayImageS, Measure.map_apply (measurable_finUnitsAt S) hA,
    withDensity_apply _ (measurable_finUnitsAt S hA), lintegral_indicator (measurable_finUnitsAt S hA)]
end GroundTheory.Automorphic.GodementSection
