-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ClockLowerV13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:02:18.002003+00:00
-- url     : https://prove2.me/submissions/ced12452-e663-49fb-b2f7-015c0664a560

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (a b : NNReal)
    (e : ℝ) (he : 0 < e) (hgap : ∀ u ∈ Icc a b, e ≤ |x u|) :
    (b : WithTop NNReal) ≤ (⨆ n : ℕ, ⨅ k : ℕ, if a ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤) := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt he
  refine le_trans ?_ (le_iSup (fun n : ℕ => ⨅ k : ℕ,
    if a ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1) then (q k : WithTop NNReal) else ⊤) n)
  apply le_iInf
  intro k
  split
  · rename_i hk
    apply WithTop.coe_le_coe.mpr
    by_contra! hb
    exact (not_lt_of_ge (hgap (q k) ⟨hk.1,hb.le⟩)) (hk.2.trans hn)
  · exact le_top
