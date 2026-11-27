-- Prove2me | solution 1 for GlobalTheory.ThetaExh.Check.rowSize_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:33:32.129159+00:00
-- url     : https://prove2.me/submissions/7e67a046-9bf9-4e80-8ef9-25367cbeff14

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
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
open GlobalTheory GlobalTheory.ThetaExh GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.ThetaExh.Check
theorem _root_.solution (hq : ∀ w : PlE H, 1 < (normV w : ℕ)) (h : RowSizeLe N A) : RowSize N A := by
  intro i σ hσ w hw hu α hα
  refine lt_of_le_of_lt (h i σ hσ w hw hu α hα) ?_
  apply Real.rpow_lt_rpow_of_exponent_lt
  · exact_mod_cast hq w
  · have hrt : R.r < R.t := by
      have h5 := R.rank_add_five_le
      simp only [Ranks.r]
      omega
    have hrt' : (R.r : ℝ) < R.t := by exact_mod_cast hrt
    linarith
end GlobalTheory.ThetaExh.Check
