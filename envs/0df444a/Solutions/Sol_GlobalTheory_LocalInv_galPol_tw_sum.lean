-- Prove2me | solution 1 for GlobalTheory.LocalInv.galPol_tw_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:51.743023+00:00
-- url     : https://prove2.me/submissions/f4117475-a70a-4e51-bd04-cd46e6ec8a6c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_galPol_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) (s : ℝ) :
    galPol A (A.lpTw (A.lpSum a b) s) = galPol A (A.lpTw a s) * galPol A (A.lpTw b s) := by
  rw [A.lpTw_sum, galPol_sum N A _ _ ((A.unr_tw _ _).2 ha) ((A.unr_tw _ _).2 hb)]
end GlobalTheory.LocalInv
