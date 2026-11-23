-- Prove2me | solution 1 for GlobalTheory.Tw.eq_zero_of_dot_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:53.477533+00:00
-- url     : https://prove2.me/submissions/5dd22859-a92c-4c6c-9b2b-73b12fb8a429

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ}
open scoped ComplexOrder
namespace GlobalTheory.Tw
theorem _root_.solution {v : Fin n → ℂ} (h : v ⬝ᵥ star v = 0) : v = 0 := dotProduct_self_star_eq_zero.1 h
end GlobalTheory.Tw
