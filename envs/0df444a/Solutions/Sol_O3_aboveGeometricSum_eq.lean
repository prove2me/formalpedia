-- Prove2me | solution 1 for O3.aboveGeometricSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:04.884084+00:00
-- url     : https://prove2.me/submissions/3c43e513-f1de-4009-8eee-f15481da88ad

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {c ratio : ℝ} (hratio : ratio ≠ 1) (S : ℕ) :
    ∑ s ∈ Finset.range S, c * ratio ^ s =
      c * ((ratio ^ S - 1) / (ratio - 1)) := by
  rw [← Finset.mul_sum, geom_sum_eq hratio]
end O3
