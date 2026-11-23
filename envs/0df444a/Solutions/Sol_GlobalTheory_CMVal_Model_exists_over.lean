-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.exists_over
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:20.949838+00:00
-- url     : https://prove2.me/submissions/13b5daef-5607-45c6-be32-b55fe1efcace

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Model
theorem _root_.solution (v : HeightOneSpectrum (OF E)) : ∃ P : HeightOneSpectrum (𝓞 E), Over P v := by
  have := v.isPrime
  obtain ⟨⟨P, hP, hl⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 E)
  exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl.over.symm⟩
end GlobalTheory.CMVal.Model
