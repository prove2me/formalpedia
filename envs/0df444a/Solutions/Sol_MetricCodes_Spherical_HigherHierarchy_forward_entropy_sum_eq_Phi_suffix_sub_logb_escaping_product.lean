-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.forward_entropy_sum_eq_Phi_suffix_sub_logb_escaping_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/068ca65f-5da6-4915-9564-53748e745261

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_eq_sum_entropy_gaps
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sum_neg_logb_eq_neg_logb_compactifiedEscapingRatioProduct

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
open scoped BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r k j : ℕ} (hkj : k + j = r)
    (A : Fin (r + 1) → ℝ) (B d : Fin r → ℝ)
    (hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i) :
    (∑ i : Fin r,
      if A i.castSucc = 0 then -Real.logb 2 (d i)
      else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
        MetricCodes.sphericalEntropy ((B i)⁻¹ - 1)) +
      MetricCodes.sphericalEntropy ((A (Fin.last r))⁻¹ - 1) =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) -
          Real.logb 2 (compactifiedEscapingRatioProduct hkj d) := by
  classical
  subst r
  have hkj : k + j = k + j := rfl
  rw [Fin.sum_univ_add]
  have hprefix :
      (∑ i : Fin k,
        if A (i.castAdd j).castSucc = 0
        then -Real.logb 2 (d (i.castAdd j))
        else MetricCodes.sphericalEntropy
          ((A (i.castAdd j).castSucc)⁻¹ - 1) -
          MetricCodes.sphericalEntropy ((B (i.castAdd j))⁻¹ - 1)) =
        -Real.logb 2 (compactifiedEscapingRatioProduct hkj d) := by
    rw [← sum_neg_logb_eq_neg_logb_compactifiedEscapingRatioProduct
      hkj d hd]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i.castAdd j).val < k := i.isLt
    rw [if_pos ((hzero (i.castAdd j)).mpr hi)]
    congr 2
  have hsuffix :
      (∑ i : Fin j,
        if A (i.natAdd k).castSucc = 0
        then -Real.logb 2 (d (i.natAdd k))
        else MetricCodes.sphericalEntropy
          ((A (i.natAdd k).castSucc)⁻¹ - 1) -
          MetricCodes.sphericalEntropy ((B (i.natAdd k))⁻¹ - 1)) =
        ∑ i : Fin j,
          (MetricCodes.sphericalEntropy
            ((compactifiedAmbientSuffix hkj A i.castSucc)⁻¹ - 1) -
            MetricCodes.sphericalEntropy
              ((compactifiedStabilizerSuffix hkj B i)⁻¹ - 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : ¬ (i.natAdd k).val < k := by
      simp only [Fin.val_natAdd]
      omega
    rw [if_neg (mt (hzero (i.natAdd k)).mp hi)]
    congr 2
  rw [hprefix, hsuffix,
    Phi_eq_sum_entropy_gaps
      (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
      (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1)]
  have hterminal :
      compactifiedAmbientSuffix hkj A (Fin.last j) =
        A (Fin.last (k + j)) := by
    unfold compactifiedAmbientSuffix
    congr 1
  rw [hterminal]
  ring
end MetricCodes.Spherical.HigherHierarchy
