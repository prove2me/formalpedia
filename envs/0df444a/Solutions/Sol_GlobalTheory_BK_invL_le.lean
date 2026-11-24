-- Prove2me | solution 1 for GlobalTheory.BK.invL_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:00:13.920837+00:00
-- url     : https://prove2.me/submissions/d9151d2e-198e-4589-a942-9b2ece38059d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial

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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
include l
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution {B B' : Subalgebra O K⟦X⟧} [HasK B'] (h : B ≤ B') : invL l B ≤ B' := by
  rintro f ⟨n, hn⟩
  have := B'.mul_mem (HasK.C_mem (((l : K) ^ n)⁻¹)) (h hn)
  convert this using 1
  have h2 : (((l : B) : K⟦X⟧)) = C (l : K) := by simp
  rw [h2, ← map_pow, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (l_ne_zero l)),
    map_one, one_mul]
end GlobalTheory.BK
