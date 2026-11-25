-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSection.finUnitAt_finUnitSingle_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:50.455801+00:00
-- url     : https://prove2.me/submissions/3d27a5b1-7f72-489d-8395-f2db3aaff74a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_FiniteIdeleDecomp
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_of_ne


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
namespace GroundTheory.Automorphic.GodementSection
theorem _root_.solution {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (a : (v.adicCompletion K)ˣ) : finUnitAt w (finUnitSingle v a) = 1 :=
  Units.ext (IdeleGroup.finiteAdeleSingle_apply_of_ne h (a : v.adicCompletion K))
end GroundTheory.Automorphic.GodementSection
