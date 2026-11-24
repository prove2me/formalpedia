-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.nabla_smul_tot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:40.38977+00:00
-- url     : https://prove2.me/submissions/f0c0610c-d41a-40e7-963a-b0821735404c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_xiExt_smul_tot
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
    P.nabla (f • v) = derTot f • v + f • P.nabla v := by
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [← xiExt_smul_tot, nabla_xiExt, nabla_xiExt, ← xiExt_smul_tot, ← xiExt_smul_tot, ← map_add]
  congr 1
  ext τ i : 2
  simp [derTot, add_comm, mul_comm]
end GlobalTheory.BK.PhiMod
