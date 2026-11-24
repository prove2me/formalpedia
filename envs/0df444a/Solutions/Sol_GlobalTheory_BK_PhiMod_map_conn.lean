-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.map_conn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:34.47681+00:00
-- url     : https://prove2.me/submissions/ca8c87ba-830a-43d9-b773-c5b77cd6e791

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_eq_sum_bas
import Theorems.Thm_GlobalTheory_BK_cst_single
import Theorems.Thm_GlobalTheory_BK_PhiMod_xiExt_smul_tot
import Theorems.Thm_GlobalTheory_BK_PhiMod_map_xi
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_smul_tot
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
theorem _root_.solution {Q : PhiMod O K l e a κ} (g : Vec K a ι →+ Vec K a κ)
    (σ : (ZMod a → K⟦X⟧) → ZMod a → K⟦X⟧) (hσ : ∀ f, σ (NTot f) = NTot (σ f))
    (hs : ∀ f v, g (f • v) = σ f • g v) (hg : ∀ v, g (P.phi v) = Q.phi (g v)) (v : Vec K a ι) :
    g (P.conn v) = Q.conn (g v) := by
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [eq_sum_bas w]
  simp only [map_sum, xiExt_smul_tot, ← cst_single, ← xi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conn_smul_tot, conn_xi, smul_zero, add_zero, hs, hs, conn_smul_tot, map_xi hg, conn_xi,
    smul_zero, add_zero, hσ]
end GlobalTheory.BK.PhiMod
