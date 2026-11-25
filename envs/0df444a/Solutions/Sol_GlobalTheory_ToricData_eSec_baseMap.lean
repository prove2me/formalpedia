-- Prove2me | solution 1 for GlobalTheory.ToricData.eSec_baseMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:48:29.807295+00:00
-- url     : https://prove2.me/submissions/6ab6e236-2dfc-423e-92ce-64dc65b93e39

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
theorem _root_.solution :
    eSec (toricPre K' X q').P.A ≫ baseMap q f q' = spMap f ≫ eSec (toricPre K X q).P.A :=
  (left_baseMap q f q' η[(toricPre K' X q').P.A]).trans
    ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
      (congrArg (spMap f ≫ ·) (left_eq_hom η[(toricPre K X q).P.A]).symm)))
end GlobalTheory.ToricData
