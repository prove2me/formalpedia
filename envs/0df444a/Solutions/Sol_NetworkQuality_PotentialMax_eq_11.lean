-- Prove2me | solution 1 for NetworkQuality.PotentialMax.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T20:03:53.196395+00:00
-- url     : https://prove2.me/submissions/fdbacfeb-55d3-40d5-997a-4fb501d50826

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting
open NetworkQuality.PotentialMax

open Market
theorem solution{n : ℕ} (M : Market n) (hM : M.Standing) (i : Fin n) (B : Finset (Fin n))
    (hi : i ∉ B) (p q : ℝ) :
    M.u i (insert i B) p q - M.u i B p q =
      M.v i * (M.pot (insert i B) p q - M.pot B p q) := by
  have hv := hM.2.1 i
  unfold Market.u Market.pot
  rw [if_pos (Finset.mem_insert_self _ _), if_neg hi, Finset.card_insert_of_notMem hi,
    Finset.sum_range_succ, Finset.sum_insert hi]
  field_simp
  ring
