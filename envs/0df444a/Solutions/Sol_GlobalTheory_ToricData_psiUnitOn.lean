-- Prove2me | solution 1 for GlobalTheory.ToricData.psiUnitOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:33:26.132622+00:00
-- url     : https://prove2.me/submissions/df37e9e6-f372-425b-8d9e-7b38dd995a31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination

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
variable (K : Type) [CommRing K] [IsDomain K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable {K X}
variable (q : X → (FractionRing K)ˣ)
namespace GlobalTheory.ToricData
theorem _root_.solution (y : X) (u : Kˣ) (h : (q y : FractionRing K) = algebraMap K _ u) :
    PsiUnitOn (toricPre K X q) y Set.univ := by
  intro j V _ _ _ h'
  exact ⟨DegPre.toOpen V (u : K), u.isUnit.map _, psi_eq_toOpen q y u h j V h'⟩
end GlobalTheory.ToricData
