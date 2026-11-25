-- Prove2me | solution 1 for GlobalTheory.LevDesc.cutLat_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:59.935816+00:00
-- url     : https://prove2.me/submissions/5178f224-8d49-4bae-a959-423a1e2249a7

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
theorem _root_.solution (N : Submodule O C) : cutLat N 0 = ⊥ :=
  Submodule.ext fun F => (mem_cutLat_iff IsIdempotentElem.zero).trans
    ⟨fun h => Subtype.ext h.2.symm, fun h => by obtain rfl : F = 0 := h; exact ⟨N.zero_mem, rfl⟩⟩
end GlobalTheory.LevDesc
