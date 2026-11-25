-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.pullLE_bijective_of_le_opensRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:43:41.446221+00:00
-- url     : https://prove2.me/submissions/d6b6dc88-c48f-4f7d-ab2f-82b915851dcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechLBPullIsoOfIsOpenImmersion
import Theorems.Thm_GlobalTheory_AbLaw_bijective_appLE_of_le_opensRange
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_coord_pullLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
namespace SecOn
theorem _root_.solution {Y Y' : Scheme.{0}} (M : LB Y) (e : Y' ⟶ Y)
    [IsOpenImmersion e] {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens}
    (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (SecOn.pullLE M e V V' h) := by
  have hb (i : M.ι) : Function.Bijective (e.appLE (V ⊓ M.U i) (V' ⊓ (M.pull e).U fun _ => i)
      ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))).hom :=
    bijective_appLE_of_le_opensRange e (inf_le_left.trans hV) _
      (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
  refine ⟨fun s t hst => GlobalTheory.LB.sec_ext fun i => (hb i).1 ?_, fun t => ?_⟩
  · exact (SecOn.coord_pullLE e h s fun _ => i).symm.trans
      ((congrArg (GlobalTheory.LB.coord · fun _ => i) hst).trans (SecOn.coord_pullLE e h t fun _ => i))
  · choose a ha using fun i => (hb i).2 (GlobalTheory.LB.coord t fun _ => i)
    refine ⟨GlobalTheory.LB.mkSec a fun i j => ?_, GlobalTheory.LB.sec_ext fun j =>
      (SecOn.coord_pullLE e h _ j).trans (ha (j PUnit.unit))⟩
    have e₁ : V' ⊓ (M.pull e).U (fun _ => i) ⊓ (M.pull e).U (fun _ => j) ≤
        e ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
      inf_le_inf ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))
        (GlobalTheory.LB.pull_U_le (L := M) e fun _ => j)
    refine (bijective_appLE_of_le_opensRange e (inf_le_left.trans (inf_le_left.trans hV)) e₁
      (inf_le_inf (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
        (GlobalTheory.LB.pull_U (L := M) e fun _ => j).ge)).1 ?_
    have := GlobalTheory.LB.coord_mem t (fun _ => i) (fun _ => j)
    rw [← ha i, ← ha j, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE] at this
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG]
    exact this.trans (congrArg (· * _) (GlobalTheory.LB.resG_pull_g (L := M) e (fun _ => i) (fun _ => j) _))
end SecOn
end GlobalTheory.AbLaw
