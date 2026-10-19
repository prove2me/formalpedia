-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_log_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/82ed882d-e451-4aaf-bda3-757626b8cc05

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ → ℝ) (H : ℝ)
    (hf : ∀ i n, 0 < f i n)
    (hlim : ∀ i, Tendsto (fun n : ℕ => Real.log (f i n) / (n : ℝ))
      atTop (𝓝 H)) :
    Tendsto (fun n : ℕ => Real.log (∑ i, f i n) / (n : ℝ))
      atTop (𝓝 H) := by
  classical
  let s : Finset ι := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  let M : ℕ → ℝ := fun n =>
    s.sup' hs (fun i => Real.log (f i n) / (n : ℝ))
  have hM : Tendsto M atTop (𝓝 H) := by
    simpa [M, Finset.sup'_const] using
      (Filter.Tendsto.finset_sup'_nhds_apply
        hs (fun i (_ : i ∈ s) => hlim i))
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast hs.card_pos
  have herr : Tendsto
      (fun n : ℕ => Real.log (s.card : ℝ) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have hupper : Tendsto
      (fun n : ℕ => M n + Real.log (s.card : ℝ) / (n : ℝ))
      atTop (𝓝 H) := by
    simpa using hM.add herr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hM hupper
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    apply Finset.sup'_le hs _
    intro i hi
    apply div_le_div_of_nonneg_right _ hnreal.le
    apply Real.log_le_log (hf i n)
    exact Finset.single_le_sum (fun j _ => (hf j n).le) hi
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hbound : ∀ i ∈ s, f i n ≤ Real.exp ((n : ℝ) * M n) := by
      intro i hi
      apply Real.le_exp_of_log_le
      have hsup : Real.log (f i n) / (n : ℝ) ≤ M n := by
        exact Finset.le_sup' (fun i => Real.log (f i n) / (n : ℝ)) hi
      simpa [mul_comm] using (div_le_iff₀ hnreal).mp hsup
    have hsum :
        (∑ i ∈ s, f i n) ≤
          (s.card : ℝ) * Real.exp ((n : ℝ) * M n) := by
      simpa [nsmul_eq_mul] using
        (s.sum_le_card_nsmul (fun i => f i n)
          (Real.exp ((n : ℝ) * M n)) hbound)
    have hsumpos : 0 < ∑ i ∈ s, f i n := by
      exact Finset.sum_pos (fun i _ => hf i n) hs
    have hlog := Real.log_le_log hsumpos hsum
    rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    change Real.log (∑ i ∈ s, f i n) / (n : ℝ) ≤ _
    apply (div_le_iff₀ hnreal).2
    calc
      Real.log (∑ i ∈ s, f i n) ≤
          Real.log (s.card : ℝ) + (n : ℝ) * M n := hlog
      _ = (M n + Real.log (s.card : ℝ) / (n : ℝ)) * (n : ℝ) := by
        field_simp
        ring
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
