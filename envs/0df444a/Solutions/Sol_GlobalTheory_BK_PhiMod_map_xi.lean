-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.map_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:33.794039+00:00
-- url     : https://prove2.me/submissions/7d579e0f-4eb2-43d2-9284-e3c30250581f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_mem_uPow_one
import Theorems.Thm_GlobalTheory_BK_PhiMod_raises_phi
import Theorems.Thm_GlobalTheory_BK_Raises_eq_zero
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_xi
import Theorems.Thm_GlobalTheory_BK_PhiMod_red_phi
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
variable {P}
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {Q : PhiMod O K l e a κ} {g : Vec K a ι → Vec K a κ}
    (hg : ∀ v, g (P.phi v) = Q.phi (g v)) (d : P.D) : g (P.xi d) = Q.xi (red (g (P.xi d))) := by
  rw [← sub_eq_zero]
  refine Q.raises_phi.eq_zero (σ := P.phiD) P.phiD.surjective
    (δ := fun d => g (P.xi d) - Q.xi (red (g (P.xi d)))) (fun d => ?_) (fun d => ?_) d
  · rw [mem_uPow_one, map_sub, red_xi, sub_self]
  · simp only [← phi_xi, hg, red_phi, map_sub]
end GlobalTheory.BK.PhiMod
