-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSection.isOpen_intUnitsAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:51:41.938796+00:00
-- url     : https://prove2.me/submissions/999f56e6-a70b-4ab6-bafd-828d537d19e2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_FiniteIdeleDecomp
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_units_adicCompletionIntegers


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
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Automorphic.GodementSection
theorem _root_.solution : IsOpen (intUnitsAt v : Set (v.adicCompletion K)ˣ) :=
  IdeleGroup.isOpen_units_adicCompletionIntegers K v
end GroundTheory.Automorphic.GodementSection
