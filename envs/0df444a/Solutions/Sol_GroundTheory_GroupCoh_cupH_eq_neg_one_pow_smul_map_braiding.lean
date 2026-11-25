-- Prove2me | solution 1 for GroundTheory.GroupCoh.cupH_eq_neg_one_pow_smul_map_braiding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:04:08.811385+00:00
-- url     : https://prove2.me/submissions/667349b6-b59b-4704-bd18-b9222b0d2922

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
import Definitions.Def_GroundTheory_TateCohomology_CupGraded
import Theorems.Thm_GroundTheory_GroupCoh_revCochain_cupCochain
import Theorems.Thm_GroundTheory_GroupCoh_iCocycles_cocyclesMap
import Theorems.Thm_GroundTheory_GroupCoh_iCocycles_cyclesMap_revHom
import Theorems.Thm_P2M_GroundTheory_GroupCoh___cyclesMap_revHom_bb8ed231e974
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cupH___fa07882c353c
import Theorems.Thm_P2M_GroundTheory_GroupCoh_map___apply_e7888b2277b6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (h : p + q = n) (h' : q + p = n)
    (x : groupCohomology A p) (y : groupCohomology B q) :
    cupH h x y = (-1 : k) ^ (p * q) • map (MonoidHom.id G) (β_ B A).hom n (cupH h' y x) := by
  refine groupCohomology_induction_on x fun z => ?_
  refine groupCohomology_induction_on y fun w => ?_
  have key : HomologicalComplex.cyclesMap (revHom (A ⊗ B)) n (cupCocycles h z w) =
      (-1 : k) ^ (p * q) • cocyclesMap (MonoidHom.id G) (β_ B A).hom n
        (cupCocycles h' (HomologicalComplex.cyclesMap (revHom B) q w)
          (HomologicalComplex.cyclesMap (revHom A) p z)) := by
    refine cocycles_ext ?_
    rw [iCocycles_cyclesMap_revHom, map_smul, iCocycles_cocyclesMap, iCocycles_cupCocycles]
    erw [iCocycles_cupCocycles]
    rw [iCocycles_cyclesMap_revHom, iCocycles_cyclesMap_revHom]
    funext x
    exact revCochain_cupCochain h h' _ _ x
  rw [cupH_π, ← π_cyclesMap_revHom (cupCocycles h z w), key, map_smul, ← map_π_apply]
  erw [← cupH_π]
  rw [π_cyclesMap_revHom, π_cyclesMap_revHom]
end GroundTheory.GroupCoh
