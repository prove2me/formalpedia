-- Prove2me | solution 1 for GlobalTheory.UU.KerPair.exists_pow_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:37.759786+00:00
-- url     : https://prove2.me/submissions/d4df88c7-62d1-4721-ab3d-db00ca5dac60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOfGen
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.KerPair
namespace GlobalTheory.UU.KerPair
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  induction n with
  | zero =>
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (0 : ℕ))
      (fun U _ h => by simp) (LB.oneGen L (Y := Y))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t', ht', fun Z r z J hJ => (hv _ _ z J hJ).trans ((val_one _).trans (pow_zero _).symm)⟩
  | succ n ih =>
    obtain ⟨s, hs, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (n + 1 : ℕ)) (fun U _ h => by
        refine (Fintype.prod_sum_type _).trans ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← zpow_add]
        congr 1
        push_cast
        ring)
      (LB.mulGen L _ _ _ _ s t) (DVR.mulGen_isGen _ _ _ _ _ _ _ hs ht)
    refine ⟨t', ht', fun Z r z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
    rw [hv Z r z J hJ, pow_succ]
end GlobalTheory.UU.KerPair
