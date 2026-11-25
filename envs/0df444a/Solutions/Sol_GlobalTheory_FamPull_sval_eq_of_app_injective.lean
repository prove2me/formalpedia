-- Prove2me | solution 1 for GlobalTheory.FamPull.sval_eq_of_app_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:52:14.454133+00:00
-- url     : https://prove2.me/submissions/d299ecb3-da5f-43fa-92b3-7ae9b865e58a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
namespace GlobalTheory.FamPull
theorem _root_.solution {X Y Y' : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u : LB.Sec (LB.LinComb M φ ε)} {u' : LB.Sec (LB.LinComb M φ' ε')}
    (h : ∀ y J, Good M y J → sval u κ y J = sval u' κ y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good M z J) : sval u r z J = sval u' r z J := by
  obtain ⟨t, hv⟩ := exists_sec hM hF u'
  have e : ∀ j, u.f j = t.f j := fun j => by
    refine hκ (LB.wchart M φ j) (fn_ext fun y hy => ?_)
    choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
    refine (gs_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') κ y _ hy _).symm)
    rw [Category.id_comp]
    exact (sec_trans u κ y hy (Good.mem hI φ κ)).trans ((congrArg _ ((h y I hI).trans (hv _ κ y I hI).symm)).trans
      (sec_trans t κ y hy (Good.mem hI φ κ)).symm)
  exact (congrArg (gs r z _) (e _)).trans (hv Z r z J hJ)
end GlobalTheory.FamPull
