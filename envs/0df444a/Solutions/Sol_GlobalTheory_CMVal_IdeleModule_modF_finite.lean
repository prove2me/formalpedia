-- Prove2me | solution 1 for GlobalTheory.CMVal.IdeleModule.modF_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:24.787379+00:00
-- url     : https://prove2.me/submissions/758d4f97-511a-4c78-a4ab-935e18069476

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleModule
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.IdeleModule
theorem _root_.solution (y : (Af E)ˣ) : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v ((y : Af E) v)))).Finite := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]
end GlobalTheory.CMVal.IdeleModule
