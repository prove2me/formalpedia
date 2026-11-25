-- Prove2me | solution 1 for GlobalTheory.CoordLinear.val_eq_of_levels
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:20.42481+00:00
-- url     : https://prove2.me/submissions/034801ab-8dba-411b-b7bc-78a2f2f7f4bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ESecStruct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfLevels
import Theorems.Thm_GlobalTheory_CoordLinear_fn_eq_of_levels
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


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
open GlobalTheory GlobalTheory.CoordLinear
open Geo.Tor
namespace GlobalTheory.CoordLinear
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsHausdorff I R] {X : Scheme.{0}}
    {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ e y J, Good M y J → val u (thick R I e) y J = val u' (thick R I e) y J)
    (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hM hF u hu
  choose j hj using fun k => exists_chart hM (φ' k (IsLocalRing.closedPoint R))
  have hW : LB.wchart M φ' j = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff (R := R) (LB.wchart M φ' j)).1 (Set.mem_iInter.2 hj)
  have hm : ∀ y, y ∈ LB.wchart M φ' j := fun y => by rw [hW]; trivial
  have e : t.s j = u'.s j := by
    refine Units.ext (fn_eq_of_levels I _ hW _ _ fun e => ?_)
    refine congrArg Units.val (show pullU (thick R I e) _ (t.s j) = pullU (thick R I e) _ (u'.s j) from
      unit_ext fun y _ => ?_)
    choose I₀ hI₀ using fun χ : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ X => exists_chart hM (χ y)
    refine (gm_pull _ _ y _ (hm _) _).trans (Eq.trans ?_ (gm_pull _ _ y _ (hm _) _).symm)
    rw [Category.id_comp]
    exact (gen_trans ht _ y (hm _) (Good.mem hI₀ φ' _)).trans
      ((congrArg _ ((hv _ _ y I₀ hI₀).trans (h e y I₀ hI₀))).trans (gen_trans hu' _ y (hm _) (Good.mem hI₀ φ' _)).symm)
  refine (hv Z r z J hJ).symm.trans ?_
  exact (gen_trans ht r z (hJ.mem φ' r) (hm _)).trans
    ((congrArg (fun q => _ * gm r z _ q) e).trans (gen_trans hu' r z (hJ.mem φ' r) (hm _)).symm)
end GlobalTheory.CoordLinear
