-- Prove2me | solution 1 for GlobalTheory.ToricData.lieMult_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:42:14.620082+00:00
-- url     : https://prove2.me/submissions/857ba59a-27b7-4e4d-9e72-6c97fc133ced

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
theorem _root_.solution (O : Type) [CommRing O] [StarRing O] [Module O X] (h) {F : Type} [Field F] (f : K →+* F)
    (τ : O →+* F) :
    LieMult (ofRingAct (toricOAct q O h).onB.toRingAct) (spMap f) τ 0 := ⟨Fin.elim0, fun i => i.elim0, fun w _ => ⟨Fin.elim0, ⟨Fin.elim0, fun i => i.elim0, toUnit_unique _ _⟩,
    fun c _ => funext fun i => i.elim0⟩⟩
end GlobalTheory.ToricData
