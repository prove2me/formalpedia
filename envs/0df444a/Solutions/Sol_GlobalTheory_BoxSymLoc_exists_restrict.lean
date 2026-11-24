-- Prove2me | solution 1 for GlobalTheory.BoxSymLoc.exists_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:03:58.020162+00:00
-- url     : https://prove2.me/submissions/cea6596e-5470-4eb5-8920-29cdbd152ea3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedSymBoxLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxSymLoc
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res)
open ReciprocityTheory.ChartRestriction.G.Out.LBxP
variable {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
namespace GlobalTheory.BoxSymLoc
theorem _root_.solution {S : Scheme.{0}} {A B : Over S} (f : A ⟶ B) (U : S.Opens) :
    ∃ ρ : (A.hom ⁻¹ᵁ U).toScheme ⟶ (B.hom ⁻¹ᵁ U).toScheme,
      ρ ≫ (B.hom ⁻¹ᵁ U).ι = (A.hom ⁻¹ᵁ U).ι ≫ f.left := by
  refine ⟨f.left.resLE _ _ ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  rw [← Scheme.Hom.comp_preimage, Over.w]
end GlobalTheory.BoxSymLoc
