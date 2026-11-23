-- Prove2me | solution 1 for GlobalTheory.BK.N_frob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:38.711206+00:00
-- url     : https://prove2.me/submissions/a6dd70f9-00da-4f61-b0e3-203476a1b89c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_coeff_N
import Theorems.Thm_GlobalTheory_BK_coeff_frob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) [Fact l.Prime] (f : K⟦X⟧) :
    N K (frob K l f) = (l : K⟦X⟧) * frob K l (N K f) := by
  ext n
  rw [← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul, coeff_N, coeff_frob, coeff_frob]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_N, Nat.mul_div_cancel_left _ (Fact.out : l.Prime).pos]
    push_cast; ring
  · simp
end GlobalTheory.BK
