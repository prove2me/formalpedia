-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:24.529597+00:00
-- url     : https://prove2.me/submissions/a167dddd-a123-493f-b672-b0e9097ebe77

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_adicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable {v}
variable (v)
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity (v.adicCompletion K) n] :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) =
      n ^ 2 / ‖(n : v.adicCompletion K)‖ := by
  rw [index_range_powMonoidHom_adicCompletion v (NeZero.ne n),
    HasEnoughRootsOfUnity.natCard_rootsOfUnity, sq]
end GroundTheory.Global
