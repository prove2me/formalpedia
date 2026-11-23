-- Prove2me | solution 1 for GlobalTheory.FormalInv.mem_coeffsInDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:46.680804+00:00
-- url     : https://prove2.me/submissions/56ee8935-b48a-4c8d-b830-5f6bef20dd95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_mem_coeffsIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
namespace GlobalTheory.FormalInv
theorem _root_.solution {S : Subring R} {g : ℕ} {f : MvPowerSeries σ R} :
    f ∈ coeffsInDeg σ S g ↔ ∀ d : σ →₀ ℕ, d.degree < g → coeff d f ∈ S := by
  simp only [mem_coeffsIn, degree_eq_weight_one, forall_const]
end GlobalTheory.FormalInv
