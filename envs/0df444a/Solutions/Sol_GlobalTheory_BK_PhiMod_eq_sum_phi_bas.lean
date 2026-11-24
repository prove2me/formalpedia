-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.eq_sum_phi_bas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:03:33.405963+00:00
-- url     : https://prove2.me/submissions/70f8ca1d-6148-486a-8d41-0f88ecfb0ef3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_bas
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
theorem _root_.solution (v : Vec K a ι) :
    v = ∑ i, (fun τ => (P.mxInv τ *ᵥ v τ) i) • P.phi (bas i) := by
  ext1 τ
  conv_lhs => rw [← Matrix.one_mulVec (v τ), ← P.mx_mul_mxInv τ, ← Matrix.mulVec_mulVec]
  ext1 j
  simp only [Finset.sum_apply, Pi.smul_apply', phi_bas, Pi.smul_apply, Matrix.col_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end GlobalTheory.BK.PhiMod
