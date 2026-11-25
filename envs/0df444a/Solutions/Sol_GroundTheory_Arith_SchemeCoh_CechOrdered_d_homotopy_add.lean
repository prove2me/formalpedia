-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.d_homotopy_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:13:02.232544+00:00
-- url     : https://prove2.me/submissions/3677a6c9-0aaf-4f44-8f3b-d66d0e45c510

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_hom_supp
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_bd_hom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_homotopy_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable {ι : Type w} [LinearOrder ι] {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (U : ι → Opens X)
variable {P U}
namespace GroundTheory.Arith.SchemeCoh.CechOrdered
theorem _root_.solution (q : ℕ) (σ : Cochain P U (q + 1)) :
    d P U q (homotopy P U q σ) + homotopy P U (q + 1) (d P U (q + 1) σ) =
      σ - altProj P U (q + 1) σ := by
  funext i
  rw [Pi.add_apply, Pi.sub_apply, d_apply, homotopy_apply,
    pair_d σ (supp_inter U (hom_supp (q + 1) i) fun t ht => ht), bd_hom, map_sub, map_sub,
    lin_bd_single_apply, map_sum, pair_single _ _ _ le_rfl, one_smul, res_refl, altProj_apply]
  have : ∑ a : Fin (q + 2), ((-1 : ℤ) ^ (a : ℕ)) •
      res P (inter_le_comp U i a.succAbove) (homotopy P U q σ (i ∘ a.succAbove)) =
      ∑ a : Fin (q + 2), pair σ (inter U i) (((-1 : ℤ) ^ (a : ℕ)) • hom q (i ∘ a.succAbove)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [homotopy_apply, res_pair σ _ (supp_inter U (hom_supp q _) fun t ht => ht), map_zsmul]
  rw [this]
  abel
end GroundTheory.Arith.SchemeCoh.CechOrdered
