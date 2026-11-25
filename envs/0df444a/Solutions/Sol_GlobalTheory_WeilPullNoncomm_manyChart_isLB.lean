-- Prove2me | solution 1 for GlobalTheory.WeilPullNoncomm.manyChart_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:09:35.177044+00:00
-- url     : https://prove2.me/submissions/5392dba1-d484-4987-9098-e51882f14a5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_gm_manyChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
theorem _root_.solution {X : Scheme.{0}} {κ : Type} [Nonempty κ] (v : κ → Γ(X, ⊤)ˣ) : (manyChart v).IsLB where
  cover := top_le_iff.1 fun _ _ => TopologicalSpace.Opens.mem_iSup.2 ⟨Classical.arbitrary κ, trivial⟩
  g_self i := unit_ext fun y hy => by
    rw [gm_res (𝟙 X) y _ hy, map_one, gm_manyChart, mul_inv_cancel]
  cocycle i j k := unit_ext fun y hy => by
    rw [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_manyChart, gm_manyChart,
      gm_manyChart, _root_.mul_assoc, inv_mul_cancel_left]
end GlobalTheory.WeilPullNoncomm
