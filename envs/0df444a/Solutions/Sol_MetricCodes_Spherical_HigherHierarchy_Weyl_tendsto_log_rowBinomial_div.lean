-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_rowBinomial_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/29cd291a-633d-444b-8ed8-efc0dc71cc70

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_add_choose_div
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_tailLength_ratio

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
open scoped BigOperators Nat Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Weyl
namespace MetricCodes.Spherical.HigherHierarchy.Weyl
theorem _root_.solution
    {r : ℕ} (i : Fin (r + 1))
    (k : ℕ → ℕ) {a : ℝ} (ha : 0 < a)
    (hkTop : Tendsto k atTop atTop)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ =>
        Real.log (((k n + tailLength n r i).choose (k n) : ℝ)) /
          (n : ℝ))
      atTop
      (𝓝 ((1 + a) * Real.log (1 + a) - a * Real.log a)) := by
  have htailTop : Tendsto (fun n : ℕ => tailLength n r i) atTop atTop := by
    have h := (tendsto_sub_atTop_nat (i.val + r + 3)).comp tendsto_id
    refine h.congr' (Eventually.of_forall fun n => ?_)
    change n - (i.val + r + 3) = tailLength n r i
    unfold tailLength
    omega
  have h := SpherePacking.tendsto_log_add_choose_div
    k (fun n : ℕ => tailLength n r i) a 1 hkTop htailTop hk
    (tendsto_tailLength_ratio r i) ha (by norm_num)
  simpa [Real.log_one, add_comm] using h
end MetricCodes.Spherical.HigherHierarchy.Weyl
