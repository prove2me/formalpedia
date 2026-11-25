-- Prove2me | solution 1 for GroundTheory.Global.KummerIndex.units_map_mem_localUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:21.554626+00:00
-- url     : https://prove2.me/submissions/04f33667-2ae8-498c-a1a9-c9cfd8a2d134

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
import Theorems.Thm_GroundTheory_Global_KummerIndex_mem_localUnits_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero
open GroundTheory.Global.KummerIndex
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.KummerIndex
theorem _root_.solution {a : Kˣ} (ha : v.valuation K (a : K) = 1) :
    Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a ∈ localUnits v := by
  rw [mem_localUnits_iff, Units.coe_map]
  change Valued.v ((a : K) : v.adicCompletion K) = 1
  rw [valuedAdicCompletion_eq_valuation', ha]
end GroundTheory.Global.KummerIndex
