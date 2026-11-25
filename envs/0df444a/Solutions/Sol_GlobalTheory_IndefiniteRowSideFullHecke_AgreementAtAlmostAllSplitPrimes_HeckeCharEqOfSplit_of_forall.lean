-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.HeckeCharEqOfSplit.of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:18.066044+00:00
-- url     : https://prove2.me/submissions/e44fcb6d-c49e-44e8-aadf-f70e99cbac8a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_AgreementAtAlmostAllSplitPrimes
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AgreementAtAlmostAllSplitPrimes_agreeAtAlmostAllSplit_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes
namespace GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes
namespace HeckeCharEqOfSplit
theorem _root_.solution {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    {A : NAut N} (h : HeckeCharEqOfSplit N A) (χ χ' : A.CG 1)
    (hw : ∀ w, IsSplitPl H w → A.locG χ w = A.locG χ' w) : χ = χ' :=
  h χ χ' ((agreeAtAlmostAllSplit_iff A χ χ').2 (Filter.Eventually.of_forall hw))
end HeckeCharEqOfSplit
end GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes
