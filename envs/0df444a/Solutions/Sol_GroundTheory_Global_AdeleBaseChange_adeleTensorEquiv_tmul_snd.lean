-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_tmul_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:56.352103+00:00
-- url     : https://prove2.me/submissions/2968fe04-7bc7-47d3-9272-e01cf7b4be99

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorEquiv_tmul_apply


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
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (l : L) (a : 𝔸[K]) (w : HeightOneSpectrum (𝓞 L)) :
    (adeleTensorEquiv K L (l ⊗ₜ a)).2 w =
      SemiLocal.tensorEquiv' L (below K w) (l ⊗ₜ a.2 (below K w)) ⟨w, liesOver_below w⟩ :=
  finiteTensorEquiv_tmul_apply l a.2 w
end GroundTheory.Global.AdeleBaseChange
