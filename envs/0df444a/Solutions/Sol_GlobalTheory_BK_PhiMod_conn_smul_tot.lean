-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.conn_smul_tot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:26:14.539524+00:00
-- url     : https://prove2.me/submissions/7a88f180-776d-4645-be65-4f8b26f88c13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_nabla_smul_tot
import Theorems.Thm_GlobalTheory_BK_N_apply
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    P.conn (f • v) = NTot f • v + f • P.conn v := by
  rw [conn_apply, nabla_smul_tot, conn_apply]
  ext τ i : 2
  simp only [derTot, NTot, N_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply', smul_eq_mul]
  ring
end GlobalTheory.BK.PhiMod
