-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.card_filter_lt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:41.169802+00:00
-- url     : https://prove2.me/submissions/87819133-6aeb-4abc-95cf-9359190d02b2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_llRank_permGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (w : Equiv.Perm (Fin n)) (r j : Fin n) :
    (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j).card =
      if h : r.val + 1 < n then llRank ⟨r.val + 1, h⟩ j (permGL F w) else 0 := by
  split_ifs with h
  · rw [llRank_permGL]
    congr 1
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨hx, -⟩
    rw [Fin.lt_def] at hx
    have := x.isLt
    omega
end GroundTheory.Automorphic.Whittaker
