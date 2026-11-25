-- Prove2me | solution 1 for GlobalTheory.ToricData.baseIso_rig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:29:41.671729+00:00
-- url     : https://prove2.me/submissions/a1d9c24d-5da8-4cdb-83cd-2b0cecad8aef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
theorem _root_.solution (he : eSec (toricPre K' X q').P.A ≫ baseMap q f q' = spMap f ≫ eSec (toricPre K X q).P.A) :
    LB.Gen.Maps (LB.linCombIso (baseIso q f q') (K := PUnit) (fun _ => eSec (toricPre K' X q').P.A) (fun _ => 1))
      (toricPre K' X q').rig
      (rigPullOf (baseMap q f q') (spMap f) he (toricPre K X q).P.L (toricPre K X q).rig) := by
  intro p
  have h1 : (rigPullOf (baseMap q f q') (spMap f) he (toricPre K X q).P.L (toricPre K X q).rig).s p.1 = 1 := by
    simp only [rigPullOf]
    erw [cg_isConst, gv]
    repeat erw [map_one]
    all_goals rfl
  have h2 : (toricPre K' X q').rig.s p.2 = 1 := map_one (res _)
  have h3 : (LB.linCombIso (baseIso q f q') (K := PUnit) (fun _ => eSec (toricPre K' X q').P.A)
      (fun _ => 1)).s p = 1 := by
    simp only [LB.linCombIso, baseIso]
    refine Finset.prod_eq_one fun _ _ => ?_
    repeat erw [map_one]
    exact one_zpow _
  rw [h1, h2, h3, map_one, map_one]
  exact (_root_.mul_one _).symm
end GlobalTheory.ToricData
