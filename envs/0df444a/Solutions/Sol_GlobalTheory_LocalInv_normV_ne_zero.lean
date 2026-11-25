-- Prove2me | solution 1 for GlobalTheory.LocalInv.normV_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:00:42.691373+00:00
-- url     : https://prove2.me/submissions/6f7378ff-fffb-4133-bb63-8b619339a7b3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_one_lt_normV

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
theorem _root_.solution (w : PlE H) : ((normV w : ℕ) : ℂ) ≠ 0 := by
  have h := one_lt_normV w
  have : (normV w : ℕ) ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  exact_mod_cast this
end GlobalTheory.LocalInv
