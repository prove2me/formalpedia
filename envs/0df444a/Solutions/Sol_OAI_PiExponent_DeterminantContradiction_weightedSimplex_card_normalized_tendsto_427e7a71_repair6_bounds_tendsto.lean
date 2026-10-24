-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair6_bounds_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:55:58.038487+00:00
-- url     : https://prove2.me/submissions/844c615d-5808-4352-83f1-125897885fdc

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
open Filter Topology
open scoped BigOperators

private theorem tendsto_shifted_power_ratio (n : Nat) (c d : Real) (hd : d ≠ 0) :
    Tendsto (fun H : Real => (((H + c) ^ n / d) / H ^ n)) atTop (nhds (1 / d)) := by
  have hc : Tendsto (fun H : Real => c / H) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hbase : Tendsto (fun H : Real => 1 + c / H) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hc)
  have hratio : Tendsto (fun H : Real => (H + c) / H) atTop (nhds 1) := by
    have heq : (fun H : Real => 1 + c / H) =ᶠ[atTop]
        (fun H : Real => (H + c) / H) := by
      filter_upwards [eventually_gt_atTop (0 : Real)] with H hH
      have hHne : H ≠ 0 := ne_of_gt hH
      field_simp [hHne]
      <;> ring
    exact hbase.congr' heq
  have hpow : Tendsto (fun H : Real => ((H + c) / H) ^ n) atTop (nhds 1) := by
    simpa using hratio.pow n
  have hquot : Tendsto (fun H : Real => (((H + c) / H) ^ n) / d) atTop
      (nhds (1 / d)) := by
    simpa using hpow.div_const d
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with H hH
  have hHne : H ≠ 0 := ne_of_gt hH
  rw [div_pow]
  field_simp [hd, pow_ne_zero n hHne]
  <;> ring

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) :
    And
      (Tendsto (fun H : Real =>
        ((H - Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w))))
      (Tendsto (fun H : Real =>
        ((H + Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w)))) := by
  have hden : 0 < (n.factorial : Real) * Finset.univ.prod w := by
    apply mul_pos
    · exact_mod_cast Nat.factorial_pos n
    · exact Finset.prod_pos fun i hi => hw i
  constructor
  · simpa [sub_eq_add_neg] using
      (tendsto_shifted_power_ratio n (-(Finset.univ.sum w))
        ((n.factorial : Real) * Finset.univ.prod w) hden.ne')
  · exact tendsto_shifted_power_ratio n (Finset.univ.sum w)
      ((n.factorial : Real) * Finset.univ.prod w) hden.ne'
