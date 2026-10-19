-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactified_entropy_sum_eq_residual_sub_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/59ce0cf7-b104-4c40-9777-a463bdced673

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_forward_entropy_sum_eq_Phi_suffix_sub_logb_escaping_product
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedEscapingRatioProduct_eq_filtered

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
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r k j q : ℕ} (hkj : k + j = r)
    (A : Fin (r + 1) → ℝ) (B d : Fin r → ℝ)
    (a₀ : Fin (q + 1) → ℝ) (b₀ : Fin q → ℝ) (c : ℝ)
    (hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i)
    (hresidualPhi :
      Phi a₀ b₀ =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1))
    (hc : c = ∏ i ∈ Finset.univ.filter
      (fun i : Fin r => i.val < k), d i) :
    (∑ i : Fin r,
      if A i.castSucc = 0 then -Real.logb 2 (d i)
      else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
        MetricCodes.sphericalEntropy ((B i)⁻¹ - 1)) +
      MetricCodes.sphericalEntropy ((A (Fin.last r))⁻¹ - 1) =
        Phi a₀ b₀ - Real.logb 2 c := by
  rw [forward_entropy_sum_eq_Phi_suffix_sub_logb_escaping_product
    hkj A B d hzero hd]
  rw [← hresidualPhi, compactifiedEscapingRatioProduct_eq_filtered hkj d,
    ← hc]
end MetricCodes.Spherical.HigherHierarchy
