-- Prove2me | solution 1 for O3.aboveGeometricSum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:08:54.807899+00:00
-- url     : https://prove2.me/submissions/afb34dfb-3032-42c4-ade4-b46af1582ed8

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveGeometricSum_eq

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {c ratio : ℝ}
    (hc : 0 ≤ c) (hratio : 1 < ratio) (S : ℕ) :
    ∑ s ∈ Finset.range S, c * ratio ^ s ≤
      c * ratio ^ S / (ratio - 1) := by
  rw [aboveGeometricSum_eq hratio.ne']
  have hden : 0 < ratio - 1 := sub_pos.mpr hratio
  have hpow : 0 ≤ ratio ^ S := pow_nonneg (by linarith) _
  calc
    c * ((ratio ^ S - 1) / (ratio - 1)) =
        c * (ratio ^ S - 1) / (ratio - 1) :=
      (mul_div_assoc c (ratio ^ S - 1) (ratio - 1)).symm
    _ ≤ c * ratio ^ S / (ratio - 1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hc) hden.le
end O3
