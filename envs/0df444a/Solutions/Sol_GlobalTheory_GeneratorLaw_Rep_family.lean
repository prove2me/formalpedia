-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.Rep.family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:16:49.252848+00:00
-- url     : https://prove2.me/submissions/348aeb72-71fb-41b7-a310-bbc2e1321b98

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
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_unit
import Theorems.Thm_GlobalTheory_GeneratorLaw_compat_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
theorem _root_.solution {b : Y ⟶ X} {s : ∀ i : L.ι, Γ(Y, b ⁻¹ᵁ L.U i)ˣ} (hs : GenScheme.Compat L b s) :
    Rep L (fun _ _ k => (k b)⁻¹) (fun _ r z J => gm r z (b ⁻¹ᵁ L.U (J (r ≫ b))) (s _)) := by
  refine ⟨PUnit, inferInstance, fun _ => b, fun _ => -1,
    ⟨fun j => res (LB.wchart_le L (fun _ : PUnit => b) j PUnit.unit) (s (j PUnit.unit))⟩, fun i j => ?_,
    fun V _ k => by simp, fun Z r z J hJ => gm_res r z _ (hJ.mem (fun _ : PUnit => b) r) _⟩
  refine unit_ext fun y hy => ?_
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y i j hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm)
  rw [(compat_iff s).1 hs _ (𝟙 Y) y (i PUnit.unit) (j PUnit.unit) (Set.mem_iInter.1 hy.1 PUnit.unit)
    (Set.mem_iInter.1 hy.2 PUnit.unit)]
  simp
end Rep
end GlobalTheory.GeneratorLaw
