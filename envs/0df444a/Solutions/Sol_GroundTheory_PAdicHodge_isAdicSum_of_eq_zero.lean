-- Prove2me | solution 1 for GroundTheory.PAdicHodge.isAdicSum_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:03.708656+00:00
-- url     : https://prove2.me/submissions/93744120-ee21-492a-88a9-290734b76471

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {I}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {a : ℕ → R} {m : ℕ} (h : ∀ n, m ≤ n → a n = 0) :
    IsAdicSum I a (∑ n ∈ Finset.range m, a n) := fun k => ⟨m, fun M hM => by
  rw [← Finset.sum_range_add_sum_Ico _ hM, Finset.sum_eq_zero (fun n hn => h n (Finset.mem_Ico.1 hn).1),
    add_zero, sub_self]
  exact zero_mem _⟩
end GroundTheory.PAdicHodge
