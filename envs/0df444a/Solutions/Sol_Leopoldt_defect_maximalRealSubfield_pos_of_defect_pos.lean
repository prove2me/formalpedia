-- Prove2me | solution 1 for Leopoldt.defect_maximalRealSubfield_pos_of_defect_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-09T15:02:47.594858+00:00
-- url     : https://prove2.me/submissions/e5656d8a-fda3-4d51-b5d3-8aa8c2e9f6d3

import Theorems.Thm_Leopoldt_zpRankBelow_unitClosure_mono

open NumberField

/-- For a CM field the two unit ranks agree, so monotonicity of the `ℤ_p`-rank of the unit
closure along `K⁺ ⊆ K` turns a positive defect for `K` into a positive defect for `K⁺`. -/
theorem solution (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (K : Type*) [Field K] [NumberField K] [IsCMField K] (h : 0 < Leopoldt.defect p K) :
    0 < Leopoldt.defect p (maximalRealSubfield K) := by
  have hmono := Leopoldt.zpRankBelow_unitClosure_mono p (maximalRealSubfield K) K
  have hrank := IsCMField.units_rank_eq_units_rank K
  unfold Leopoldt.defect at h ⊢
  omega
