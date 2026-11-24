-- Prove2me | solution 1 for GlobalTheory.SecGlue.Rel.gs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:28.991177+00:00
-- url     : https://prove2.me/submissions/777ee5b7-37bc-452a-bebb-d5c435495240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
import Theorems.Thm_GlobalTheory_SecGlue_gs_appLE
import Theorems.Thm_GlobalTheory_SecGlue_mem_chart

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {A X Y Z : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {ε : K → ℤ}
namespace GlobalTheory.SecGlue
namespace Rel
theorem _root_.solution {h : Y ⟶ X} {q : X ⟶ A} {q' : Y ⟶ A} (e : h ≫ q = q')
    {s : LB.Sec (LB.LinComb L (fun _ : K => q) ε)} {t : LB.Sec (LB.LinComb L (fun _ : K => q') ε)}
    (H : Rel h s t) (j : K → L.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L (fun _ : K => q') j) :
    gs (r ≫ h) z (LB.wchart L (fun _ : K => q) j) (s.f j) =
      gs r z (LB.wchart L (fun _ : K => q') j) (t.f j) := by
  rw [← H j (fun y hy => (mem_chart e j y).1 hy)]
  exact (gs_appLE r h z _ _ _ hz _).symm
end Rel
end GlobalTheory.SecGlue
