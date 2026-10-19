-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_hierarchyStieltjesRatio_append_of_escaping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/fcd4146f-b972-4944-b89c-1267a57bbefd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyStieltjesRatio_append
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_stieltjes_pair_factor_of_degree_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_hierarchyStieltjesRatio_of_coordinatewise

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
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {k r : ℕ}
    {u v : ℕ → Fin k → ℝ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    {d : Fin k → ℝ}
    (hu : ∀ i, Tendsto (fun n => u n i) atTop atTop)
    (hd : ∀ i, Tendsto (fun n => v n i / u n i) atTop (𝓝 (d i)))
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (A i)))
    (hb : ∀ i, Tendsto (fun n => b n i) atTop (𝓝 (B i)))
    (hA : ∀ i, 0 ≤ A i)
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun n => hierarchyStieltjesRatio
        (Fin.append (m := k) (n := r + 1) (u n) (a n))
        (Fin.append (m := k) (n := r) (v n) (b n)) t)
      atTop
      (𝓝 ((∏ i : Fin k, d i ^ 2) * hierarchyStieltjesRatio A B t)) := by
  have hprefix :
      Tendsto (fun n =>
        ∏ i : Fin k,
          (t + quadraticCoordinate (v n i)) /
            (t + quadraticCoordinate (u n i)))
        atTop (𝓝 (∏ i : Fin k, d i ^ 2)) := by
    apply tendsto_finsetProd Finset.univ
    intro i _
    exact tendsto_stieltjes_pair_factor_of_degree_ratio (hu i) (hd i) t
  have htail :=
    tendsto_hierarchyStieltjesRatio_of_coordinatewise ha hb hA ht
  have hproduct := hprefix.mul htail
  apply hproduct.congr'
  filter_upwards [] with n
  exact (hierarchyStieltjesRatio_append (u n) (v n) (a n) (b n) t).symm
end MetricCodes.Spherical.HigherHierarchy
