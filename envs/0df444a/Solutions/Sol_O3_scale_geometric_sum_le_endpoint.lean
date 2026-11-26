-- Prove2me | solution 1 for O3.scale_geometric_sum_le_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:17.725914+00:00
-- url     : https://prove2.me/submissions/34210548-9ac0-4d6a-868d-f814999f53dd

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
import Theorems.Thm_O3_radius_geometric_sum_le_endpoint

set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution {a k0 : ℝ}
    (ha : 0 < a) (hk0 : 0 ≤ k0) (S : ℕ) :
    ∑ s ∈ Finset.range (S + 1), (((2 : ℝ) ^ s * k0) ^ a) ≤
      geometricAmortizationConstant a * (((2 : ℝ) ^ S * k0) ^ a) :=
  radius_geometric_sum_le_endpoint ha hk0 S
end O3
