-- Prove2me | solution 1 for GlobalTheory.ToricData.map_top_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:18.859443+00:00
-- url     : https://prove2.me/submissions/37ca77c1-79b5-4c7c-ad96-3e9d1ea356df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Theorems.Thm_GlobalTheory_ToricData_map_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ToricData
variable {Z Y : Scheme.{0}} {J J₁ J₂ J₃ : Type} [Fintype J] [Fintype J₁] [Fintype J₂] [Fintype J₃]
namespace GlobalTheory.ToricData
theorem _root_.solution {V : Y.Opens} (hV : V = ⊤) {a b : Γ(Y, ⊤)}
    (h : (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a = (Y.presheaf.map (homOfLE le_top).op).hom b) :
    a = b := by
  subst hV
  rwa [map_self, map_self] at h
end GlobalTheory.ToricData
