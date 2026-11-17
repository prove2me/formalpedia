-- Prove2me | solution 1 for KnodelPrimeCordial.edge_gcd_positive_from_bij__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T09:55:48.044322+00:00
-- url     : https://prove2.me/submissions/a1f47ae6-bb64-4e23-9b91-d25baf3185ec

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel

theorem solution (f : Fin 2 × Fin 4 → ℕ)
    (hbij : Set.BijOn f Set.univ (Set.Icc 1 8)) :
    ∀ e ∈ (KnodelPrimeCordial.knodel 3 8).edgeFinset,
      0 < KnodelPrimeCordial.edgeGcd f e := by
  have hf : ∀ x, 0 < f x := by
    intro x
    have hx : f x ∈ Set.Icc 1 8 := hbij.mapsTo (Set.mem_univ x)
    exact lt_of_lt_of_le (by decide) hx.1
  intro e he
  refine Sym2.inductionOn e ?_
  intro u v
  simpa [KnodelPrimeCordial.edgeGcd] using
    Nat.gcd_pos_of_pos_left (f v) (hf u)
