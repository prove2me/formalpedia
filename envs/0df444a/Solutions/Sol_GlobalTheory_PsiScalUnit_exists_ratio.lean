-- Prove2me | solution 1 for GlobalTheory.PsiScalUnit.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:19.039983+00:00
-- url     : https://prove2.me/submissions/4368c40a-b2c5-4ec7-a1f3-8bed01333a95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiScalarsRelationsUpToBaseUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
open GlobalTheory GlobalTheory.PsiScalUnit
namespace GlobalTheory.PsiScalUnit
theorem _root_.solution {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ w * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res r z le trivial _).symm
end GlobalTheory.PsiScalUnit
