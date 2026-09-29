-- Prove2me | solution 1 for ModularForm.coeffHeckeT_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/adcce412-2d70-5fea-a17e-83c82173c18b

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_coeffHeckeT_int

set_option autoImplicit false

open ModularForm

theorem solution (k : ℤ) (hk : 1 ≤ k) (p : ℕ) {a : ℕ → ℂ} (ha : ∀ n : ℕ, ∃ m : ℤ, a n = m) (n : ℕ) : ∃ m : ℤ, ModularForm.coeffHeckeT k p a n = m := by
  obtain ⟨m₁, hm₁⟩ := ha (n * p)
  rw [coeffHeckeT_apply, hm₁]
  split_ifs with h
  · obtain ⟨m₂, hm₂⟩ := ha (n / p)
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hk)
    refine ⟨m₁ + p ^ j * m₂, ?_⟩
    rw [hm₂, hj, zpow_natCast]
    push_cast
    ring
  · exact ⟨m₁, by simp⟩

end S_ModularForm_coeffHeckeT_int
end P2MW
export P2MW.S_ModularForm_coeffHeckeT_int (solution)
