-- Prove2me | solution 1 for GlobalTheory.LevDesc.mem_cutLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:57:15.884466+00:00
-- url     : https://prove2.me/submissions/5c55bff5-4be5-47fa-add5-243721cad92e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_mem_spanQ

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
theorem _root_.solution {N : Submodule O C} {T : Module.End K R} (hT : IsIdempotentElem T) {F : C} :
    F ∈ cutLat N T ↔ F ∈ N ∧ T F = F :=
  and_congr_right fun hF => ⟨fun ⟨x, _, e⟩ => by
      have e' : T x = F := e
      rw [← e']; exact congrArg (fun S : Module.End K R => S x) hT,
    fun e => ⟨F, mem_spanQ hF, e⟩⟩
end GlobalTheory.LevDesc
