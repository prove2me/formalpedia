-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateMap_comp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:28:11.394023+00:00
-- url     : https://prove2.me/submissions/2c4e4a92-6c11-4532-9efb-e4ca4ef1f01b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable {X Y Z : Rep k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (φ : X ⟶ Y) (ψ : Y ⟶ Z) (i : ℤ) (x : (tateComplex X).X i) :
    ((tateComplex.map (φ ≫ ψ)).f i).hom x =
      ((tateComplex.map ψ).f i).hom (((tateComplex.map φ).f i).hom x) := by
  have h := (tateComplexFunctor k G).map_comp φ ψ
  simp only [tateComplexFunctor_map] at h
  rw [h]
  rfl
end GroundTheory.GroupCoh
