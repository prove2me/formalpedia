-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSection.mem_finiteIntegralUnits_iff_forall_finUnitAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:24.509452+00:00
-- url     : https://prove2.me/submissions/4e841ac2-3f49-43c6-bf17-18240ff94cce

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_FiniteIdeleDecomp
import Theorems.Thm_GroundTheory_Automorphic_GodementSection_finUnitAt_mem_intUnitsAt_iff
import Theorems.Thm_GroundTheory_Global_mem_finiteIntegralUnits


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
theorem _root_.solution (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    b ∈ finiteIntegralUnits K ↔ ∀ w : HeightOneSpectrum (𝓞 K), finUnitAt w b ∈ intUnitsAt w := by
  rw [mem_finiteIntegralUnits]
  exact forall_congr' fun w ↦ (finUnitAt_mem_intUnitsAt_iff w b).symm
end GroundTheory.Automorphic.GodementSection
