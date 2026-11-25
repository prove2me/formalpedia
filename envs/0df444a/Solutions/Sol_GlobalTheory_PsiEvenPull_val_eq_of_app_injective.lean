-- Prove2me | solution 1 for GlobalTheory.PsiEvenPull.val_eq_of_app_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:17.623862+00:00
-- url     : https://prove2.me/submissions/3c604759-c3d9-41ea-8251-a7112790a730

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
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
open GlobalTheory GlobalTheory.PsiEvenPull
namespace GlobalTheory.PsiEvenPull
theorem _root_.solution {X Y Y' : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u κ y J = val u' κ y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hM hF u' hu'
  have e : ∀ j, u.s j = t.s j := fun j => by
    have : pullU κ (LB.wchart M φ j) (u.s j) = pullU κ (LB.wchart M φ j) (t.s j) := unit_ext fun y hy => by
      choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
      refine (gm_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') κ y _ hy _).symm)
      rw [Category.id_comp]
      exact (gen_trans hu κ y hy (Good.mem hI φ κ)).trans ((congrArg _ ((h y I hI).trans (hv _ κ y I hI).symm)).trans
        (gen_trans ht κ y hy (Good.mem hI φ κ)).symm)
    exact Units.ext (hκ _ (congrArg Units.val this))
  exact (congrArg (gm r z _) (e _)).trans (hv Z r z J hJ)
end GlobalTheory.PsiEvenPull
