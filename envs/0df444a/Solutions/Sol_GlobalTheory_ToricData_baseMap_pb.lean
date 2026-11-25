-- Prove2me | solution 1 for GlobalTheory.ToricData.baseMap_pb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:36:44.061052+00:00
-- url     : https://prove2.me/submissions/ad95a99e-5c69-43a0-bee1-8286a6579f46

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
namespace GlobalTheory.ToricData
theorem _root_.solution {K' : Type} [CommRing K'] [IsDomain K'] (f : K →+* K') (q' : X → (FractionRing K')ˣ) :
    IsGrpPullback (toricPre K' X q').P.A (toricPre K X q).P.A (spMap f) (baseMap q f q') :=
  ⟨(IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩ :
      IsPullback (spMap f) (𝟙 _) (𝟙 _) (spMap f)),
    fun _ _ _ _ _ _ _ => (left_eq_hom _).trans (left_baseMap q f q' _).symm⟩
end GlobalTheory.ToricData
