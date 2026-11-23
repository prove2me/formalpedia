-- Prove2me | solution 1 for GlobalTheory.Tw.eq_zero_of_mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:16.786241+00:00
-- url     : https://prove2.me/submissions/c6421ca4-653b-4ac0-bfc2-b5d52688a615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_eq_zero_of_dot_star

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
namespace GlobalTheory.Tw
theorem _root_.solution {V : Submodule ℂ (Fin n → ℂ)} {v : Fin n → ℂ} (h : v ∈ V) (h' : v ∈ perp V) : v = 0 :=
  eq_zero_of_dot_star (h' v h)
end GlobalTheory.Tw
