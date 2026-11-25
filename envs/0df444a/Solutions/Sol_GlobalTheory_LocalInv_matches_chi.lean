-- Prove2me | solution 1 for GlobalTheory.LocalInv.matches_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:13.655267+00:00
-- url     : https://prove2.me/submissions/296d09d5-c70e-4a4d-ac23-470c41d79b4a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_eventually_out
import Theorems.Thm_GlobalTheory_LocalInv_charRep_charpoly
import Theorems.Thm_GlobalTheory_LocalInv_iota_eps
import Theorems.Thm_GlobalTheory_LocalInv_galPol_block
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution (i : N.Loc) (j : ℕ) :
    Matches N A i (charRep N i (N.chi i 1 * eps N i ^ j)) (A.tw (A.muC i) A.etaTinv)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + j) := by
  filter_upwards [eventually_out N i] with w hw hs B σ hB hσ
  rw [galPol_block N A i (hw hs) hB hσ, charRep_charpoly]
  simp [iota_eps N A i (hw hs).2.1 hB hσ]
end GlobalTheory.LocalInv
