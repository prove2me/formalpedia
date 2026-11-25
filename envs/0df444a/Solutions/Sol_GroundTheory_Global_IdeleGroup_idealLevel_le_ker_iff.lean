-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.idealLevel_le_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:59.246377+00:00
-- url     : https://prove2.me/submissions/10529c6d-56f8-471e-897c-eee141d79848

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Theorems.Thm_GroundTheory_Global_finprod_asIdeal_pow_dvd_iff
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteLevel_le_ker_iff
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
    (hχ : Continuous χ) {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    idealLevel 𝔪 ≤ χ.ker ↔ conductor χ ∣ 𝔪 := by
  rw [idealLevel, finiteLevel_le_ker_iff hH χ hχ, conductor,
    finprod_asIdeal_pow_dvd_iff (finite_support_conductorExponentAt hH χ hχ) h𝔪]
end GroundTheory.Global.IdeleGroup
