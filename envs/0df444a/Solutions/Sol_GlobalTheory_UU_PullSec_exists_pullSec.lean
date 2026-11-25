-- Prove2me | solution 1 for GlobalTheory.UU.PullSec.exists_pullSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:14:45.445441+00:00
-- url     : https://prove2.me/submissions/e6ff8084-c15c-4bbd-a778-4504bd3ce3dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniquePullB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PullSec
variable {X X' W Y Y₂ : Scheme.{0}}
namespace GlobalTheory.UU.PullSec
theorem _root_.solution {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y₂ ⟶ X)} {φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (h : Y ⟶ Y₂) (hc : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  have h1 : (LB.oneGen L (Y := Y)).IsGen := fun i j =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨s', hs⟩ := exists_sec hL (φ' := φ') (ε' := ε) (fun U _ g => by
      refine ((Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) rfl (Fintype.prod_empty _)).trans
        (_root_.mul_one _))).trans ?_
      exact Finset.prod_congr rfl fun k _ => by rw [hc]; rfl) (pullMulSec s h (LB.oneGen L) h1)
  refine ⟨s', fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec s h _ h1 r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]
end GlobalTheory.UU.PullSec
