-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.paired_ratio_limit_pos_of_ambient_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/be59931a-be9b-4205-9387-308d0ee44a8c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_entropy_gap_le_Phi
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_degree_ratio_lower_bound_of_entropy_gap_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_paired_stabilizer_tendsto_atTop_of_ambient

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {φ : ℕ → ℕ} {C d : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (i : Fin r)
    (ha : Tendsto (fun n => a (φ n) i.castSucc) atTop atTop)
    (hratio : Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds d)) :
    0 < d := by
  have hb := paired_stabilizer_tendsto_atTop_of_ambient h hPhi i ha
  let K : ℝ := (2 * (2 : ℝ) ^ (C + 1 / Real.log 2))⁻¹
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hbound : ∀ᶠ n : ℕ in atTop,
      K ≤ b (φ n) i / a (φ n) i.castSucc := by
    filter_upwards [hb.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hbn
    apply CompactificationEntropy.degree_ratio_lower_bound_of_entropy_gap_le
      hbn ((h (φ n)).2 i).1.le
    exact (CompactificationEntropy.entropy_gap_le_Phi (h (φ n)) i).trans
      (hPhi (φ n))
  exact hK.trans_le (ge_of_tendsto hratio hbound)
end MetricCodes.Spherical.HigherHierarchy
