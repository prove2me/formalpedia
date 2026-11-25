-- Prove2me | solution 1 for GlobalTheory.LB.coord_isoOfGen_hom_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:03:31.15467+00:00
-- url     : https://prove2.me/submissions/dbe15a90-d2fb-44e6-ac08-ce08efbf56e6

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
variable {M : LB X}
namespace GlobalTheory.LB
theorem _root_.solution (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(toMod L, V)) (p : M.ι) (q : L.ι) {W : X.Opens}
    (hp : W ≤ V ⊓ M.U p) (hq : W ≤ V ⊓ L.U q) (h : W ≤ M.U p ⊓ L.U q) :
    resG X hp (coord ((isoOfGen hL hM w hw).hom.app V s) p) =
      resG X h ((show Γ(X, M.U p ⊓ L.U q)ˣ from w.s (p, q)) : Γ(X, M.U p ⊓ L.U q)) *
        resG X hq (coord s q) :=
  coord_mulFun hL hM _ s p q hp hq h
end GlobalTheory.LB
