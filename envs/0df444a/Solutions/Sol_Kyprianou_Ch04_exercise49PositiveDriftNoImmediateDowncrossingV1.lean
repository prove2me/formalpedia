-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PositiveDriftNoImmediateDowncrossingV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:31:26.228813+00:00
-- url     : https://prove2.me/submissions/75a2eeaf-7978-41b3-b54f-f85ffcfcc129

import Mathlib
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (x : NNReal → ℝ) (d : ℝ) (hd : 0 < d)
    (h : Tendsto (fun t : NNReal => x t / (t : ℝ))
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds d)) :
    (0 : WithTop NNReal) <
      sInf {u : WithTop NNReal |
        ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ x t < 0} := by
  have hp : ∀ᶠ t : NNReal in 𝓝[>] (0 : NNReal), 0 < x t / (t : ℝ) :=
    h.eventually (eventually_gt_nhds hd)
  obtain ⟨ε, hε, hεpos⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).1 hp
  have hbound (t : NNReal) (ht : 0 < t) (hx : x t < 0) :
      ε ≤ t := by
    by_contra hnot
    have hpos := hεpos (show t ∈ Ioo (0 : NNReal) ε from
      ⟨ht, lt_of_not_ge hnot⟩)
    have hneg : x t / (t : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hx.le t.coe_nonneg
    exact (not_lt_of_ge hneg) hpos
  have hinf : (ε : WithTop NNReal) ≤
      sInf {u : WithTop NNReal |
        ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ x t < 0} := by
    apply le_sInf
    intro u hu
    obtain ⟨t, rfl, ht, hx⟩ := hu
    exact_mod_cast hbound t ht hx
  exact lt_of_lt_of_le (by exact_mod_cast hε) hinf
