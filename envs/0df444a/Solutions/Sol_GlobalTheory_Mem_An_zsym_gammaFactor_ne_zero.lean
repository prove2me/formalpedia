-- Prove2me | solution 1 for GlobalTheory.Mem.An.zsym_gammaFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:54.123803+00:00
-- url     : https://prove2.me/submissions/3f4c5462-9a08-4217-8d1c-56b360c5ed34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex GlobalTheory.Mem.An
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
variable {q : ℕ}
namespace GlobalTheory.Mem.An
theorem _root_.solution (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with h | h <;> rw [h.gammaFactor_def]
  · exact Gammaℝ_ne_zero_of_re_pos hs
  · exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
end GlobalTheory.Mem.An
