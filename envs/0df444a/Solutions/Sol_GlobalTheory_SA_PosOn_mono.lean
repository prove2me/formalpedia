-- Prove2me | solution 1 for GlobalTheory.SA.PosOn.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:10:14.75931+00:00
-- url     : https://prove2.me/submissions/c0aa2704-eb6e-469c-8298-07a13cb6ba91

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram

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
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
omit [NumberField E] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace GlobalTheory.SA
namespace PosOn
theorem _root_.solution {h : V →ₗ⋆[E] V →ₗ[E] E} {U U' : Submodule E V} (hU : PosOn h U) (hle : U' ≤ U) :
    PosOn h U' := fun τ x hx => hU τ x (hle hx)
end PosOn
end GlobalTheory.SA
