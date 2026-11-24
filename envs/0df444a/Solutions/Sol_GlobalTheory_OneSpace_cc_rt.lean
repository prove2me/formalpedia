-- Prove2me | solution 1 for GlobalTheory.OneSpace.cc_rt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:34:28.425548+00:00
-- url     : https://prove2.me/submissions/2bdb191b-9e3c-473f-8a6b-4b5705ae6bde

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ConjEqNegOfSqEqNegNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace
import Theorems.Thm_GlobalTheory_OneSpace_emb_cc
import Theorems.Thm_GlobalTheory_OneSpace_conj_of_sq
import Theorems.Thm_GlobalTheory_OneSpace_emb_rt_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.OneSpace
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.OneSpace
theorem _root_.solution (H : Host E) : FD.cc (H.rt : E) = -(H.rt : E) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [emb_cc, map_neg]
  exact conj_of_sq H.d_prime.pos (emb_rt_sq H τ)
end GlobalTheory.OneSpace
