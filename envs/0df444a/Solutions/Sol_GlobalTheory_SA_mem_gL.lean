-- Prove2me | solution 1 for GlobalTheory.SA.mem_gL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:34.300228+00:00
-- url     : https://prove2.me/submissions/ac273343-00f7-4327-9413-c8f53c555368

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Theorems.Thm_GlobalTheory_SA_int_smul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open NumberField Module Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace GlobalTheory.SA
theorem _root_.solution {S : HSpace E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (x : S.V) :
    x ∈ gL Λ g ↔ ∃ y ∈ Λ, (g : E) • y = x := by
  rw [gL, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [int_smul_eq]
  rfl
end GlobalTheory.SA
