-- Prove2me | solution 1 for GlobalTheory.ToricData.baseIso_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:33:00.465099+00:00
-- url     : https://prove2.me/submissions/bcdcf8c0-0830-4198-afc6-dd4db5c7a0d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ)
variable {K' : Type} [CommRing K'] [IsDomain K']
variable (f : K →+* K') (q' : X → (FractionRing K')ˣ)
namespace GlobalTheory.ToricData
theorem _root_.solution : (baseIso q f q').IsGen := by
  intro i j
  have hg : (LB.div ((toricPre K X q).P.L.pull (baseMap q f q')) (toricPre K' X q').P.L).g i j = 1 := by
    simp only [LB.div]
    erw [linComb_triv_g]
    repeat erw [map_one]
    erw [inv_one, _root_.one_mul]
    all_goals rfl
  rw [hg, _root_.one_mul]
  exact (map_one _).trans (map_one _).symm
end GlobalTheory.ToricData
