-- Prove2me | solution 1 for GlobalTheory.BK.mx_rankOne_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:34:16.616646+00:00
-- url     : https://prove2.me/submissions/f879b43c-4ddd-4658-afb3-2eff73bf2dff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {l e}
namespace GlobalTheory.BK
theorem _root_.solution (j : ZMod a → ℤ) (τ : ZMod a) (i k : Unit) :
    (rankOne O K l e j).mx τ i k = Ezpow K l e (j τ) := by
  have h : Units.map ((invE l e (A O K)).val : invE l e (A O K) →* K⟦X⟧) (Eunit O K l e) =
      (isUnit_E l e).unit := Units.ext rfl
  rw [Ezpow, ← h, ← map_zpow]
  rw [PhiMod.mx, rankOne]
  dsimp only
  generalize Eunit O K l e ^ j τ = u
  simp
end GlobalTheory.BK
