-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.dvd_conductor_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:58.376647+00:00
-- url     : https://prove2.me/submissions/21cba0f8-0e4a-44f2-96a2-4ada9190e4bc

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Theorems.Thm_GroundTheory_Global_asIdeal_dvd_finprod_iff
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finite_support_conductorExponentAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ conductor χ ↔ 1 ≤ conductorExponentAt χ v :=
  asIdeal_dvd_finprod_iff (finite_support_conductorExponentAt hH χ hχ) v
end GroundTheory.Global.IdeleGroup
