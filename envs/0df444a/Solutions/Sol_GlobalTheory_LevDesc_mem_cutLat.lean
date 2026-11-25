-- Prove2me | solution 1 for GlobalTheory.LevDesc.mem_cutLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:02:53.84818+00:00
-- url     : https://prove2.me/submissions/cd79408d-7aa8-423f-a2c6-8c6e70c1fa0f

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
theorem _root_.solution {N : Submodule O C} {T : Module.End K R} {F : C} :
    F ∈ cutLat N T ↔ F ∈ N ∧ ∃ x ∈ spanQ N, T x = F := Iff.rfl
end GlobalTheory.LevDesc
