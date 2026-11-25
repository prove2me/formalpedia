-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSection.finUnitAt_finUnitsSingle_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:03.785116+00:00
-- url     : https://prove2.me/submissions/5a245846-f70f-447d-a02f-9d1722dc7242

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_FiniteIdeleDecomp
import Theorems.Thm_GroundTheory_Automorphic_GodementSection_finUnitAt_finUnitSingle_of_ne

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
theorem _root_.solution (a : (v : S) → (v.1.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ S) : finUnitAt w (finUnitsSingle S a) = 1 := by
  change finUnitAt w (∏ v : S, finUnitSingle v.1 (a v)) = 1
  rw [map_prod]
  refine Finset.prod_eq_one fun u _ ↦ finUnitAt_finUnitSingle_of_ne (fun h ↦ hw (by rw [h]; exact u.2)) _
end GroundTheory.Automorphic.GodementSection
