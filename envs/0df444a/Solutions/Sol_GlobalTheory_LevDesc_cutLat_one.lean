-- Prove2me | solution 1 for GlobalTheory.LevDesc.cutLat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:58.483102+00:00
-- url     : https://prove2.me/submissions/961ac798-31ea-4de0-bcfd-40c6596d3956

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_mem_cutLat_iff

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
theorem _root_.solution (N : Submodule O C) : cutLat N 1 = N :=
  Submodule.ext fun _ => (mem_cutLat_iff IsIdempotentElem.one).trans (and_iff_left rfl)
end GlobalTheory.LevDesc
