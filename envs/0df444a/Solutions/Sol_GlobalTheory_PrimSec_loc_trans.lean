-- Prove2me | solution 1 for GlobalTheory.PrimSec.loc_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:29:54.250664+00:00
-- url     : https://prove2.me/submissions/4b894106-62db-4e62-8e7c-f1e33fcc705c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
import Theorems.Thm_GlobalTheory_PrimSec_app_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {X XK : Scheme.{0}} {j : XK ⟶ X} {M : LB X}
namespace GlobalTheory.PrimSec
theorem _root_.solution (σ : LB.Sec (M.pull j)) (i k : M.ι) {V : X.Opens} (hi : V ≤ M.U i) (hk : V ≤ M.U k) :
    loc σ i hi = (j.app V).hom (rs X (le_inf hi hk) (M.g i k).val) * loc σ k hk := by
  have h := congrArg (rs XK (le_inf (le_pull M j hi) (le_pull M j hk))) (σ.compat (fun _ => i) (fun _ => k))
  rw [map_mul] at h
  refine (rs_rs _ _ _).symm.trans (h.trans ?_)
  refine congrArg₂ (· * ·) ?_ (rs_rs _ _ _)
  rw [app_rs]
  have e : (M.pull j).g (fun _ => i) (fun _ => k) = res (fun _ hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit,
      Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (M.pull j).U (fun _ => i) ⊓ (M.pull j).U (fun _ => k) ≤
        j ⁻¹ᵁ (M.U i ⊓ M.U k)) (pullU j _ (M.g i k)) := by
    change ∏ _ : PUnit, _ ^ (1 : ℤ) = _
    rw [Fintype.prod_unique]
    exact zpow_one _
  rw [e]
  exact rs_rs _ _ _
end GlobalTheory.PrimSec
