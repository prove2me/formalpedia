-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.plus_conn_xVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:39:56.26652+00:00
-- url     : https://prove2.me/submissions/fc68b6ae-0590-497a-99a7-9a8d783952b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_Hom_app_conn
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_extension_generator_eq_add
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_phi_extension_generator_eq_zeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution : (P.plus hy).conn xVec = (P.plusInl hy).app (P.zeta y - P.conn y) := by
  rw [map_sub, ← conn_phi_extension_generator_eq_zeta, phi_extension_generator_eq_add, map_add, Hom.app_conn, add_sub_cancel_right]
end GlobalTheory.BK.PhiMod
