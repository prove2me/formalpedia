-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.xi_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:26:49.561857+00:00
-- url     : https://prove2.me/submissions/b37e1af8-1822-4e14-a60b-60f5712a3876

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_mem_uPow_one
import Theorems.Thm_GlobalTheory_BK_PhiMod_raises_phi
import Theorems.Thm_GlobalTheory_BK_Raises_eq_zero
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_xi
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
theorem _root_.solution {s : P.D → Vec K a ι} (h0 : ∀ d, red (s d) = d)
    (h : ∀ d, P.phi (s d) = s (P.phiD d)) (d : P.D) : s d = P.xi d := by
  rw [← sub_eq_zero]
  refine P.raises_phi.eq_zero (σ := P.phiD) P.phiD.surjective
    (δ := fun d => s d - P.xi d) (fun d => ?_) (fun d => ?_) d
  · rw [mem_uPow_one, map_sub, red_xi, h0, sub_self]
  · simp only [← phi_xi, ← h, map_sub]
end GlobalTheory.BK.PhiMod
