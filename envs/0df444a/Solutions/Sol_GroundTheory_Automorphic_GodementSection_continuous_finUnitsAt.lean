-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSection.continuous_finUnitsAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:41.110885+00:00
-- url     : https://prove2.me/submissions/4e32d203-ebf1-4a43-8ec8-ae9ad0948940

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_FiniteIdeleDecomp
import Theorems.Thm_GroundTheory_Automorphic_GodementSection_continuous_finUnitAt

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
namespace GroundTheory.Automorphic.GodementSection
theorem _root_.solution : Continuous (finUnitsAt (K := K) S) :=
  continuous_pi fun v ↦ continuous_finUnitAt v.1
end GroundTheory.Automorphic.GodementSection
