-- Prove2me | solution 1 for GlobalTheory.UU.ExpLinC.sval_lincomb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:46:36.972983+00:00
-- url     : https://prove2.me/submissions/5ef75c6e-6c56-4d73-ad69-eea674cb9753

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalLincomb
import Theorems.Thm_P2M_GlobalTheory_UU_ExpLinC_gs_sum__4b10aeea308e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ExpLinC
namespace GlobalTheory.UU.ExpLinC
theorem _root_.solution {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {t : Fin n → LB.Sec (LB.LinComb L φ ε)} {t' : LB.Sec (LB.LinComb L φ ε)} (a : Fin n → Γ(Y, ⊤))
    (h : ∀ j, t'.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (a i) * (t i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t' r z J = ∑ i, gs r z ⊤ (a i) * sval (t i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_sum' _ _ _ hm _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact (gs_mul _ _ _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm (a i)))
end GlobalTheory.UU.ExpLinC
