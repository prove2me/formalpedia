-- Prove2me | solution 1 for GlobalTheory.UT.TorusWeight.val_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:52.415718+00:00
-- url     : https://prove2.me/submissions/ca834c1d-66d9-4f5b-b270-31193103526c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TxFrameOfOne
import Theorems.Thm_GlobalTheory_UT_TorusWeight_gs_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.TorusWeight
namespace GlobalTheory.UT.TorusWeight
theorem _root_.solution {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (a : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → (val t (𝟙 _) y J).val = gs (𝟙 _) y ⊤ a) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    (val t r z J).val = gs r z ⊤ a := by
  have hJ' : Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ (r ≫ ψ)
  have e := h (r z) _ hJ'
  rw [val_of t (𝟙 _) (r z) _ (fun k => J (r ≫ φ k)) (fun k => by rw [Category.id_comp])] at e
  have hm := hJ.mem φ r
  refine (gs_unit r z _ hm _).symm.trans ((gs_map r z _ hm _).trans (Eq.trans ?_ (gs_map r z ⊤ trivial a).symm))
  exact congrArg _ ((gs_unit (𝟙 Y) (r z) _ hm _).trans e)
end GlobalTheory.UT.TorusWeight
