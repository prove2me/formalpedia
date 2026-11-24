-- Prove2me | solution 1 for GlobalTheory.OneSpace.im_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:21.640891+00:00
-- url     : https://prove2.me/submissions/e48e851a-077c-4263-8458-0b69ff4ccea9

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
theorem _root_.solution (τ : E →+* ℂ) {ξ : E} (h : FD.cc ξ = -ξ) (h0 : ξ ≠ 0) : (τ ξ).im ≠ 0 := by
  intro hi
  have h1 := emb_cc τ ξ
  rw [h, map_neg] at h1
  have h2 := congrArg Complex.re h1
  simp at h2
  apply h0
  apply τ.injective
  rw [map_zero]
  apply Complex.ext <;> simp [hi]
  linarith
end GlobalTheory.OneSpace
