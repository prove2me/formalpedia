-- Prove2me | solution 1 for GlobalTheory.ToricData.toricPre_tate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:47:05.6578+00:00
-- url     : https://prove2.me/submissions/2f84e701-a2df-467b-948c-dd4f1ae7521a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Theorems.Thm_GlobalTheory_ToricData_unitOn_zpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
variable (F : Type) [Field F] [Algebra (FractionRing K) F]
namespace GlobalTheory.ToricData
theorem _root_.solution : toricPre InhTate.R ℤ (fun n => piK ^ (n ^ 2)) = tatePre := by
  unfold toricPre tatePre P0 pi0
  congr 1
  funext n
  exact congrArg (cg _ _) (unitOn_zpow _ _)
end GlobalTheory.ToricData
