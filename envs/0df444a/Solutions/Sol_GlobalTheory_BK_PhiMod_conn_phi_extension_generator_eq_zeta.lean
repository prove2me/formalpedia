-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.conn_phi_extension_generator_eq_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:59.984044+00:00
-- url     : https://prove2.me/submissions/ca8196d6-ca21-4c93-b931-e958d3fc6a34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_zeta_phi_sub
import Theorems.Thm_GlobalTheory_BK_Hom_app_zeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_extension_generator_eq_add

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
theorem _root_.solution : (P.plus hy).conn ((P.plus hy).phi xVec) = (P.plusInl hy).app (P.zeta y) := by
  rw [Hom.app_zeta, ← zeta_phi_sub, phi_extension_generator_eq_add, add_sub_cancel_left]
end GlobalTheory.BK.PhiMod
