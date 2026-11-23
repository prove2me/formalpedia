-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.mem_dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:02.898809+00:00
-- url     : https://prove2.me/submissions/8306806b-5f7f-4e1a-9606-2e01ec200992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution {C J : Ideal (𝓞 K)} (hC : C ≠ 0) : J ∈ dv C ↔ J ∣ C := by
  simp only [dv, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_iff_right_iff_imp]
  intro h
  have hC' : Ideal.absNorm C ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hC
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hC') (map_dvd Ideal.absNorm h)
end GlobalTheory.Hk.RaySq
