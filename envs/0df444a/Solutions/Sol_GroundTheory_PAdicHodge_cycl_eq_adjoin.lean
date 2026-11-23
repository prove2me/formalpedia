-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cycl_eq_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:45.593237+00:00
-- url     : https://prove2.me/submissions/7fa325fc-dd22-47c3-ab0a-a219cac84a80

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    cycl p n = ℚ_[p]⟮ζ⟯ := by
  apply le_antisymm
  · rw [cycl, adjoin_le_iff]
    intro x (hx : x ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (mem_adjoin_simple_self ℚ_[p] ζ) i
  · rw [adjoin_simple_le_iff]
    exact pow_eq_one_mem_cycl hζ.pow_eq_one
end GroundTheory.PAdicHodge
