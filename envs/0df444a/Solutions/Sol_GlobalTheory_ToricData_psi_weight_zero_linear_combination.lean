-- Prove2me | solution 1 for GlobalTheory.ToricData.psi_weight_zero_linear_combination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:34:02.123863+00:00
-- url     : https://prove2.me/submissions/1c3d5f75-87d8-4c26-96bc-6e444485709f

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
theorem _root_.solution (O : Type) [CommRing O] [StarRing O] [Module O X] (h) (w : O)
    (hw : ∀ y, polar q y (w • y) = q y) :
    TraceFormTwistIso (toricPre K X q) (toricOAct q O h) w := by
  unfold TraceFormTwistIso
  exact ⟨cg _ _ 1, cg_isGen _ _ 1,
    corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _),
    fun y => corr_of_isConst ((isConst_mulGen (tau_isConst q y (w • y))
      ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq
        (congrArg (fun z => unitOn z * 1) (hw y))) (isConst_mulGen (psi_isConst q y) (rigK_isConst q))⟩
end GlobalTheory.ToricData
