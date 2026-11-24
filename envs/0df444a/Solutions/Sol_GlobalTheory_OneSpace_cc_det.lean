-- Prove2me | solution 1 for GlobalTheory.OneSpace.cc_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:12.412798+00:00
-- url     : https://prove2.me/submissions/c3e67464-c104-4965-bc4d-628e80698e83

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
theorem _root_.solution {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (h : ∀ a b, FD.cc (G a b) = G b a) :
    FD.cc G.det = G.det := by
  have h1 : IsCMField.complexConj E G.det = (G.map (IsCMField.complexConj E)).det :=
    RingHom.map_det (IsCMField.complexConj E).toRingEquiv.toRingHom G
  have h2 : G.map (IsCMField.complexConj E) = Gᵀ := by
    ext a b
    exact h a b
  rw [FD.cc, h1, h2, det_transpose]
end GlobalTheory.OneSpace
