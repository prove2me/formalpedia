-- Prove2me | solution 1 for GlobalTheory.LB.isoOfGen_hom_app_genSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:59:15.938718+00:00
-- url     : https://prove2.me/submissions/523fe951-8c36-4d55-8659-642fe43d5b5e

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
import Theorems.Thm_GlobalTheory_LB_coord_isoOfGen_hom_app
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



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
    {a : LB.Gen L} {b : LB.Gen M} (ha : a.IsGen) (hb : b.IsGen) (h : LB.Gen.Maps w a b)
    (V : X.Opens) :
    (isoOfGen hL hM w hw).hom.app V (ofSec (DVR.genSec a ha) V) = ofSec (DVR.genSec b hb) V :=
  sec_ext_of_cover hL.cover fun p q => by
    have l : V ⊓ M.U p ⊓ L.U q ≤ M.U p ⊓ L.U q := inf_le_inf_right _ inf_le_right
    rw [coord_isoOfGen_hom_app hL hM w hw _ p q _ (inf_le_inf_right _ inf_le_left) l]
    have e : resG X inf_le_left ((b.s p : Γ(X, M.U p))) =
        ((show Γ(X, M.U p ⊓ L.U q)ˣ from w.s (p, q)) : Γ(X, M.U p ⊓ L.U q)) *
          resG X inf_le_right (a.s q : Γ(X, L.U q)) := congrArg Units.val (h (p, q))
    have := congrArg (resG X l) e
    simp only [map_mul, resG_resG] at this
    simp only [coord_ofSec, resG_resG]
    exact this.symm
end GlobalTheory.LB
