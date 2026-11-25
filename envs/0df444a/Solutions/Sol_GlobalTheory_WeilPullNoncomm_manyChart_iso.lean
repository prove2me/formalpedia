-- Prove2me | solution 1 for GlobalTheory.WeilPullNoncomm.manyChart_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:56.438291+00:00
-- url     : https://prove2.me/submissions/295c1789-3f0c-4ae1-ac4d-54bb52bd463a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_gm_manyChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilPullNoncomm
open GlobalTheory.CommPairing
namespace GlobalTheory.WeilPullNoncomm
theorem _root_.solution {X Y : Scheme.{0}} {κ : Type} (v : κ → Γ(X, ⊤)ˣ) (F : X ⟶ Y) :
    LBIso (manyChart v) ((oneChart Y).pull F) := by
  refine ⟨⟨fun p => res le_top (v p.2)⁻¹⟩, (isGen_iff _).2 fun Z f z j j' k k' hj hj' hk hk' => ?_⟩
  have e : ∀ (j : (oneChart Y).ι) (k : κ), gw (L := oneChart Y) (L' := manyChart v) (F := F)
      ⟨fun p => res le_top (v p.2)⁻¹⟩ f z j k = (gm f z ⊤ (v k))⁻¹ := fun j k =>
    (gm_res f z (V := ((oneChart Y).pull F).U (fun _ => j) ⊓ ⊤) le_top ⟨mem_pull.2 trivial, trivial⟩ _).trans (map_inv _ _)
  rw [e, e, gm_manyChart]
  show _ = gm _ _ _ 1 * _ * _
  rw [map_one, _root_.one_mul, mul_inv_rev, inv_inv, mul_comm (gm f z ⊤ (v k')), mul_inv_cancel_right]
end GlobalTheory.WeilPullNoncomm
