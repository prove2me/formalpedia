-- Prove2me | solution 1 for GroundTheory.GroupCoh.map_cupH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:13.590865+00:00
-- url     : https://prove2.me/submissions/16ebe18c-a74a-4a88-9a26-cf5bfca68e1b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cupH___fa07882c353c
import Theorems.Thm_P2M_GroundTheory_GroupCoh_map___apply_e7888b2277b6
import Theorems.Thm_GroundTheory_GroupCoh_iCocycles_cocyclesMap
import Theorems.Thm_GroundTheory_GroupCoh_tensorHom_cupCochain


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
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution {A' B' : Rep k G} (φ : A ⟶ A') (ψ : B ⟶ B') (h : p + q = n)
    (a : groupCohomology A p) (b : groupCohomology B q) :
    map (MonoidHom.id G) (φ ⊗ₘ ψ) n (cupH h a b) =
      cupH h (map (MonoidHom.id G) φ p a) (map (MonoidHom.id G) ψ q b) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  have key : cocyclesMap (A := A ⊗ B) (MonoidHom.id G) (φ ⊗ₘ ψ) n (cupCocycles h z w) =
      cupCocycles h (cocyclesMap (MonoidHom.id G) φ p z) (cocyclesMap (MonoidHom.id G) ψ q w) := by
    refine cocycles_ext ?_
    rw [iCocycles_cocyclesMap, iCocycles_cupCocycles, iCocycles_cupCocycles, iCocycles_cocyclesMap,
      iCocycles_cocyclesMap]
    funext x
    exact tensorHom_cupCochain φ ψ h _ _ x
  rw [cupH_π, map_π_apply, map_π_apply, cupH_π, ← key]
  exact map_π_apply _ _
end GroundTheory.GroupCoh
