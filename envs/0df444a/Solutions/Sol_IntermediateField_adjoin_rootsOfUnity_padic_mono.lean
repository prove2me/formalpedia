-- Prove2me | solution 1 for IntermediateField.adjoin_rootsOfUnity_padic_mono
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/93b222a2-a43d-5a12-b700-5acd138f4aa6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_adjoin_rootsOfUnity_padic_mono

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField

theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) {N N' : ℕ} (h : N ∣ N') :
    IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} ≤
      IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1} := by
  apply IntermediateField.adjoin.mono
  intro ζ hζ
  obtain ⟨k, rfl⟩ := h
  obtain ⟨c, hc⟩ : q ^ N - 1 ∣ q ^ (N * k) - 1 := by
    rw [pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (q ^ N) k
  change ζ ^ (q ^ (N * k) - 1) = 1
  rw [hc, pow_mul, show ζ ^ (q ^ N - 1) = 1 from hζ, one_pow]

end S_IntermediateField_adjoin_rootsOfUnity_padic_mono
end P2MW
export P2MW.S_IntermediateField_adjoin_rootsOfUnity_padic_mono (solution)
