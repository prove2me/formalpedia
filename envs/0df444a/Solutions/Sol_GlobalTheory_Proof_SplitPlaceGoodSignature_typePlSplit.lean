-- Prove2me | solution 1 for GlobalTheory.Proof.SplitPlaceGoodSignature.typePlSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:19.97435+00:00
-- url     : https://prove2.me/submissions/dff085ea-9afc-4576-b6c6-8d5f47c07234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_ThetaLiftOfEachRow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SplitPlaceGoodSignature
import Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_isSplitPl_of_not_isConjPl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.SplitPlaceGoodSignature
open NumberField Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
variable (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.Proof.SplitPlaceGoodSignature
theorem _root_.solution : TypePlSplit N A := fun k v =>
  isSplitPl_of_not_isConjPl _ (A.plGw_nconj k v v)
end GlobalTheory.Proof.SplitPlaceGoodSignature
