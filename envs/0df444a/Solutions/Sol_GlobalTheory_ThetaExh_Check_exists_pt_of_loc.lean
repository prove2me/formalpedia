-- Prove2me | solution 1 for GlobalTheory.ThetaExh.Check.exists_pt_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:33:25.759508+00:00
-- url     : https://prove2.me/submissions/adb8daee-a74d-4404-9023-beaaa2b84bbb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Theorems.Thm_GlobalTheory_ThetaExh_Check_iotaO_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaExh GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.ThetaExh.Check
theorem _root_.solution (i : N.Loc) (h : PtLocal N A i) (P P' : A.AV i) (x : N.X i)
    (hx : A.ptV i P' = some x) (hl : ∀ w, SplitOut N i w → A.locV i P w = A.locV i P' w) :
    ∃ y, A.ptV i P = some y ∧ ∀ w, SplitOut N i w → heckePol N i y w = heckePol N i x w := by
  have hpol : ∀ w, SplitOut N i w → (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := by
    intro w hw
    rw [hl w hw]
    exact A.pt_loc i P' x hx w hw
  obtain ⟨y, hy⟩ := h P x (fun w hw => ⟨heckePol N i x w, hpol w hw, rfl⟩)
  refine ⟨y, hy, fun w hw => ?_⟩
  apply Polynomial.map_injective (iotaO N A i) (iotaO_inj N A i)
  rw [hpol w hw]
  exact A.pt_loc i P y hy w hw
end GlobalTheory.ThetaExh.Check
