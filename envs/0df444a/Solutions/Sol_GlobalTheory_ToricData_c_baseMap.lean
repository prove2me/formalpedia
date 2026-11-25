-- Prove2me | solution 1 for GlobalTheory.ToricData.c_baseMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:28:51.545907+00:00
-- url     : https://prove2.me/submissions/77366053-0d95-47f7-8a2d-2ac02c91a09d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective

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
theorem _root_.solution (y' y : X) :
    ((toricPre K' X q').c y').left ≫ baseMap q f q' = spMap f ≫ ((toricPre K X q).c y).left :=
  end_baseMap q f q' ((toricPre K' X q').c y') ((toricPre K X q).c y)
end GlobalTheory.ToricData
