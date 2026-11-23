-- Prove2me | solution 1 for GlobalTheory.BK.frob_mem_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:41.111377+00:00
-- url     : https://prove2.me/submissions/c9fb4a62-f494-4552-8ea9-36e424d61657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
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
namespace GlobalTheory.BK
theorem _root_.solution (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : f ∈ A O K) : frob K l f ∈ A O K := by
  intro n
  rw [coeff_frob]
  split_ifs
  · exact hf _
  · simp
end GlobalTheory.BK
