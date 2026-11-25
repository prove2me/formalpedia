-- Prove2me | solution 1 for GlobalTheory.ThetaExh.Check.speh_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:22:31.164808+00:00
-- url     : https://prove2.me/submissions/0637767c-c932-4332-aae5-fb99885f4cd1

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


section
noncomputable section
namespace GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
private theorem foldr_lpSum_lpChar_comm {ι : Type} (hL : ParamLaws N A) (χ : A.CG 1) (w : PlE H)
    (c : ι → ℝ) (b : A.LP w) (L : List ι) :
    L.foldr (fun k acc => A.lpSum (A.lpTw (A.lpChar b (A.locG χ w)) (c k)) acc) (A.lpZero w) =
      A.lpChar (L.foldr (fun k acc => A.lpSum (A.lpTw b (c k)) acc) (A.lpZero w)) (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction L with
  | nil => exact ((hL w).2.1 _ hd).symm
  | cons k L ih =>
    simp only [List.foldr_cons]
    rw [ih, (hL w).1 _ _ _ hd, (hL w).2.2.1 _ _ _ hd]
end GlobalTheory.ThetaExh.Check
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaExh GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.ThetaExh.Check
theorem _root_.solution (hL : ParamLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  simp only [A.locG_tw]
  exact foldr_lpSum_lpChar_comm N A hL χ w (fun k : ℝ => ((p.d : ℝ) - 1) / 2 - k) (A.locG p.π w) _
end GlobalTheory.ThetaExh.Check
