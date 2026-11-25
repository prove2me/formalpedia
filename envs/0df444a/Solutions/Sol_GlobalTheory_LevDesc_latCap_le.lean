-- Prove2me | solution 1 for GlobalTheory.LevDesc.latCap_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:02:50.437741+00:00
-- url     : https://prove2.me/submissions/55376318-88db-4901-90fb-94a3dc91718a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R O : Type} [Group G] [Field K] [CommRing R] [Algebra K R] [CommRing O] [Algebra O K]
  {C : Submodule K R} [Module O C] [IsScalarTower O K C]
namespace GlobalTheory.LevDesc
theorem _root_.solution (L : Submodule O C) (W : Submodule K R) : latCap L W ≤ L := inf_le_left
end GlobalTheory.LevDesc
