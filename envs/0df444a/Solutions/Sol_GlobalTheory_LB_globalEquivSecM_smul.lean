-- Prove2me | solution 1 for GlobalTheory.LB.globalEquivSecM_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:59:13.438083+00:00
-- url     : https://prove2.me/submissions/aef6c0c4-ce6b-4b94-85a1-2b7d3795111a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
variable (L : LB X)
variable {L}
open MonoidalCategory CartesianMonoidalCategory ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L₀ : LB A.left) (a : ℤ) (T : Over S)
namespace GlobalTheory.LB
theorem _root_.solution (r : Γ(T.left, ⊤)) (s : Γ(toMod (LPow A L₀ a T), ⊤)) :
    globalEquivSecM A L₀ a T ((show Γ((T ⊗ A).left, ⊤) from (fst T A).left.appTop r) • s) =
      r • globalEquivSecM A L₀ a T s :=
  congrArg (SecM.ofSec A) (map_smul (globalEquiv _) _ s)
end GlobalTheory.LB
