-- Prove2me | solution 1 for GlobalTheory.BK.nontrivial_Ahat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:47.553339+00:00
-- url     : https://prove2.me/submissions/93c56c41-8bee-4d6b-b0c8-b3a9969d40ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.hat_coe
attribute [local simp] GlobalTheory.BK.coe_Eunit

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.BK
theorem _root_.solution [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] :
    Nontrivial (Ahat O K l e) := by
  have h : idE O K l e ^ 1 ≠ ⊤ := by
    rw [pow_one, Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : E K l e * g = 1 := congrArg Subtype.val hg
    have : (g : K⟦X⟧) = 0 := eq_zero_of_E_mul l e (invL_A_le_Rpi l e g.2) fun n => by
      rw [hg', coeff_one, if_neg (by have := NeZero.pos e; omega)]
    simp [this] at hg'
  have := Ideal.Quotient.nontrivial_iff.2 h
  exact (AdicCompletion.evalₐ (idE O K l e) 1).toRingHom.domain_nontrivial
end GlobalTheory.BK
