-- Prove2me | solution 1 for GlobalTheory.DescTheta.isQuasicoherent_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:45.457801+00:00
-- url     : https://prove2.me/submissions/f856aa6a-582e-41ac-99a5-bb9aa8c3f8ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_restrict


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
namespace GlobalTheory.DescTheta
theorem _root_.solution {G : Over X} {L : LB G.left} (h : PushInvertible G L) :
    ((Scheme.Modules.pushforward G.hom).obj (toMod L)).IsQuasicoherent := by
  choose V hV θ hθ h1 h2 using h
  refine QCoh.isQuasicoherent_of_restrict _ (fun x => (V x).ι) (fun x => ⟨x, ?_⟩) fun x => ?_
  · rw [Scheme.Opens.opensRange_ι]; exact hV x
  · have e := Descent.freeIso (F := (Scheme.Modules.pushforward G.hom).obj (toMod L))
      (s := mkSec (θ x) (hθ x)) (Descent.bijective_smul_stalk fun W hW => by
        refine (Function.bijective_iff_existsUnique _).2 fun (s : Γ(toMod L, G.hom ⁻¹ᵁ W)) => ?_
        refine (existsUnique_congr fun a => ?_).1 (h1 x W hW _ (coord_mem s))
        refine ⟨fun h => sec_ext (L := L) fun i => (h i).symm, fun h i => ?_⟩
        exact (congrArg (fun t => coord (L := L) t i) h).symm)
    exact (SheafOfModules.isQuasicoherent (V x).toScheme.ringCatSheaf).prop_of_iso ((trivIso _).symm ≪≫ e)
      (isQuasicoherent_toMod (Out.Inh.trivLB_isLB _))
end GlobalTheory.DescTheta
