-- Prove2me | solution 1 for GlobalTheory.UU.BoxSec.Rep.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:46:13.612659+00:00
-- url     : https://prove2.me/submissions/3cc2e9dc-4bc5-42e1-85ea-dce5711b2a18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_mulSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BoxSec
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)
variable {L Y}
namespace GlobalTheory.UU.BoxSec
namespace Rep
theorem _root_.solution {P P' v v'} (h : Rep L Y P v) (h' : Rep L Y P' v') :
    Rep L Y (fun U _ h => P U h * P' U h) (fun T r z J => v T r z J * v' T r z J) := by
  obtain ⟨K, _, φ, ε, s, hP, hv⟩ := h
  obtain ⟨K', _, φ', ε', s', hP', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, H1.SectionArithmetic.mulSec s s', fun U _ h => ?_, fun T r z J hJ => ?_⟩
  · exact DVR.prod_sum₂ _ (hP U h) (hP' U h)
  · rw [H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ, hv T r z J hJ, hv' T r z J hJ]
end Rep
end GlobalTheory.UU.BoxSec
