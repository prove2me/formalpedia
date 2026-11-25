-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.Rep.unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:16:48.331637+00:00
-- url     : https://prove2.me/submissions/8702ddbd-616c-46c1-8de4-48d779643b51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
import Theorems.Thm_GlobalTheory_GeneratorLaw_mem_empty
import Theorems.Thm_GlobalTheory_GenScheme_res_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GeneratorLaw
variable {X Y Y' : Scheme.{0}} {L : LB X}
namespace GlobalTheory.GeneratorLaw
namespace Rep
theorem _root_.solution (a : Γ(Y, ⊤)ˣ) : Rep L (fun _ _ _ => 1) (fun _ r z _ => gm r z ⊤ a) := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ⟨fun j => res le_top a⟩, fun i j => ?_,
    fun V _ k => by simp, fun Z r z J _ => gm_res r z _ (mem_empty _ _) _⟩
  have hg : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
    simp [LB.LinComb]; rfl
  rw [hg]
  exact (GenScheme.res_res _ _ _).trans ((GenScheme.res_res _ _ _).symm.trans (_root_.one_mul _).symm)
end Rep
end GlobalTheory.GeneratorLaw
