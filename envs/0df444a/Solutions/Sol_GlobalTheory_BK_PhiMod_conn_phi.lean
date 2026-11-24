-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.conn_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:41:44.092472+00:00
-- url     : https://prove2.me/submissions/9e863fe9-3cf1-4363-b934-0710dcae2259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_xiExt
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_xiExt
import Theorems.Thm_GlobalTheory_BK_N_frob
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
theorem _root_.solution (v : Vec K a ι) : P.conn (P.phi v) = (l : K) • P.phi (P.conn v) := by
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [phi_xiExt, conn_xiExt, conn_xiExt, phi_xiExt, ← map_smul]
  congr 1
  ext τ i : 2
  simp only [Matrix.mulVec, dotProduct, map_sum, Pi.smul_apply, Finset.smul_sum, frobV_apply,
    Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul, N_frob, smul_comm, smul_eq_C_mul (a := (l : K)),
    map_natCast]
end GlobalTheory.BK.PhiMod
