-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.plus_phi_join
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:22.396317+00:00
-- url     : https://prove2.me/submissions/a8bedc11-0859-4961-bd68-47bbe467a8b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_apply
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
variable (P : PhiMod O K l e a ι) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (P.plus hy).phi (join v f) = join (P.phi v + frobTot K a l f • y) (frobTot K a l f) := by
  ext1 τ
  rw [phi_apply, plus, mx_ofMatrix]
  ext1 i
  rcases i with i | i <;>
    simp [join, Matrix.mulVec, dotProduct, phi_apply, Fintype.sum_sum_type, mul_comm]
end GlobalTheory.BK.PhiMod
