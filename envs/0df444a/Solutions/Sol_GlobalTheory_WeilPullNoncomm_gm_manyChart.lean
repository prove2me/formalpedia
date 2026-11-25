-- Prove2me | solution 1 for GlobalTheory.WeilPullNoncomm.gm_manyChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:31.064481+00:00
-- url     : https://prove2.me/submissions/ce98bc01-e9dd-458a-858a-202446cd6445

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
theorem _root_.solution {X Y : Scheme.{0}} {κ : Type} (v : κ → Γ(X, ⊤)ˣ) (f : Y ⟶ X) (y : Y) (i j : κ) :
    gm f y ((manyChart v).U i ⊓ (manyChart v).U j) ((manyChart v).g i j) = gm f y ⊤ (v i) * (gm f y ⊤ (v j))⁻¹ :=
  (gm_res f y (U := ⊤) (V := ⊤ ⊓ ⊤) inf_le_left ⟨trivial, trivial⟩ _).trans (by rw [map_mul, map_inv])
end GlobalTheory.WeilPullNoncomm
