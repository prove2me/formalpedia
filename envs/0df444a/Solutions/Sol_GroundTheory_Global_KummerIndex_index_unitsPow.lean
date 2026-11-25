-- Prove2me | solution 1 for GroundTheory.Global.KummerIndex.index_unitsPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:04:10.706389+00:00
-- url     : https://prove2.me/submissions/4878d66a-d7b1-4183-b9b8-35da3af5c415

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
import Theorems.Thm_GroundTheory_Global_KummerIndex_hasEnoughRootsOfUnity_of_ringHom
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity
import Theorems.Thm_GroundTheory_Global_norm_natCast_adicCompletion_eq_one


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
theorem _root_.solution (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) :
    (unitsPow (v.adicCompletion K) p).index = p ^ 2 := by
  have := hasEnoughRootsOfUnity_of_ringHom (algebraMap K (v.adicCompletion K)) p
  have h := index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity v (n := p)
  rw [norm_natCast_adicCompletion_eq_one hv, div_one] at h
  exact_mod_cast h
end GroundTheory.Global.KummerIndex
