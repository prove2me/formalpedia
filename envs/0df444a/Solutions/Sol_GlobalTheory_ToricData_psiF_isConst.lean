-- Prove2me | solution 1 for GlobalTheory.ToricData.psiF_isConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:08.943888+00:00
-- url     : https://prove2.me/submissions/68ae892c-f2b5-4840-aba0-fc4565aca059

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Theorems.Thm_GlobalTheory_ToricData_pullTop_unitOn


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
omit [Algebra (FractionRing K') F]
namespace GlobalTheory.ToricData
theorem _root_.solution (y : X) :
    IsConst (LB.pullGen _ _ _ ((toricPre K X q).psi y) (jFK (R := K) F))
      (unitOn (Units.map (algebraMap (FractionRing K) F).toMonoidHom (q y))) :=
  (isConst_pullGen (psi_isConst q y) _).of_eq (pullTop_unitOn _ _)
end GlobalTheory.ToricData
