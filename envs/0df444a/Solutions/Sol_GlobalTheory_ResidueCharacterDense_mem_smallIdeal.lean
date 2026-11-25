-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.mem_smallIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:37:36.03843+00:00
-- url     : https://prove2.me/submissions/bd4272e6-46c4-47fa-98f6-fb9c3901d612

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution {F Ω : Type} [Field F] [NormedField Ω] [IsUltrametricDist Ω]
    (σ : F →+* Ω) (x : 𝓞 F) : x ∈ smallIdeal σ ↔ ‖σ x‖ < 1 := Iff.rfl
end GlobalTheory.ResidueCharacterDense
