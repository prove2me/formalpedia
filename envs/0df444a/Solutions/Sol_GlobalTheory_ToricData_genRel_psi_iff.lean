-- Prove2me | solution 1 for GlobalTheory.ToricData.genRel_psi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:25.920905+00:00
-- url     : https://prove2.me/submissions/6fac3fed-8197-4c10-8c38-54e31ca5fac9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Theorems.Thm_GlobalTheory_ToricData_psiF_isConst
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
variable (F : Type) [Field F] [Algebra (FractionRing K') F] [Algebra (FractionRing K) F]
namespace GlobalTheory.ToricData
theorem _root_.solution
    (hF : ∀ x, algebraMap (FractionRing K) F (algebraMap K _ x) = algebraMap (FractionRing K') F (algebraMap K' _ (f x)))
    (y' y : X) (x : F) :
    GenRel (baseIso q f q') (LB.pullGen _ _ _ ((toricPre K' X q').psi y') (jFK (R := K') F))
        (LB.pullGen _ _ _ ((toricPre K X q).psi y) (jFK (R := K) F)) x ↔
      algebraMap (FractionRing K') F (q' y') = x * algebraMap (FractionRing K) F (q y) := by
  refine (genRel_baseIso_iff q f q' (psiF_isConst q' F y') (psiF_isConst q F y) x).trans (and_iff_right fun _ => ?_)
  exact pointF_baseMap q f q' F hF
    ((Over.homMk (jFK (R := K') F) rfl : TF (R := K') F ⟶ TK K') ≫ toUnit (TK K') ≫ (toricPre K' X q').c y')
    ((Over.homMk (jFK (R := K) F) rfl : TF (R := K) F ⟶ TK K) ≫ toUnit (TK K) ≫ (toricPre K X q).c y)
end GlobalTheory.ToricData
