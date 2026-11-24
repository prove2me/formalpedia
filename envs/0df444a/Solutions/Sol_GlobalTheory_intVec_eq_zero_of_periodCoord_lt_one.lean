-- Prove2me | solution 1 for GlobalTheory.intVec_eq_zero_of_periodCoord_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:35.707699+00:00
-- url     : https://prove2.me/submissions/7763e54f-8890-41c1-a614-d2bb77a9210a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Theorems.Thm_GlobalTheory_periodCoordFst_apply
import Theorems.Thm_GlobalTheory_periodCoordSnd_apply
import Theorems.Thm_GlobalTheory_ofIntVec_eq_ofRealVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (n n' : ι → ℤ)
    (h₁ : ∀ i, |periodCoordFst τ (τ *ᵥ ofIntVec n + ofIntVec n') i| < 1)
    (h₂ : ∀ i, |periodCoordSnd τ (τ *ᵥ ofIntVec n + ofIntVec n') i| < 1) :
    n = 0 ∧ n' = 0 := by
  rw [ofIntVec_eq_ofRealVec n, ofIntVec_eq_ofRealVec n'] at h₁ h₂
  rw [periodCoordFst_apply hτ] at h₁
  rw [periodCoordSnd_apply hτ] at h₂
  constructor
  · ext i
    have := h₁ i
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)
  · ext i
    have := h₂ i
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)
end GlobalTheory
