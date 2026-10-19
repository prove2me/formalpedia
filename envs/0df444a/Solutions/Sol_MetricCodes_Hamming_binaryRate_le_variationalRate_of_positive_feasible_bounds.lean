-- Prove2me | solution 1 for MetricCodes.Hamming.binaryRate_le_variationalRate_of_positive_feasible_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/63e5d4df-5cac-43e6-a42f-7bcf8a21ed56

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_binaryEntropy_nonneg
import Theorems.Thm_MetricCodes_Hamming_rateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Hamming_exists_positive_feasible_of_zero
import Theorems.Thm_MetricCodes_Hamming_binaryRate_le_of_positive_feasible_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hbound : ∀ ⦃a b : ℝ⦄,
      Feasible δ a b → 0 < b →
        ∀ᶠ n : ℕ in atTop,
          (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
            spectralPrefactor δ a b * windowFibreQuotient a b n) :
    binaryRate δ ≤ variationalRate δ := by
  have hcandidate :
      ∀ ⦃a b : ℝ⦄, Feasible δ a b →
        binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
    intro a b hfeasible
    rcases hfeasible.1.eq_or_lt with hzero | hpositive
    · have hbzero : b = 0 := hzero.symm
      subst b
      obtain ⟨c, hc, hfeasible'⟩ :=
        exists_positive_feasible_of_zero hfeasible
      have hrate := binaryRate_le_of_positive_feasible_bound
        hfeasible' hc (hbound hfeasible' hc)
      have hcunit : c ≤ 1 := by
        have hca := hfeasible'.2.1
        have hahalf := hfeasible'.2.2.1
        linarith
      have hentropy : 0 ≤ MetricCodes.binaryEntropy c :=
        MetricCodes.binaryEntropy_nonneg hc.le hcunit
      calc
        binaryRate δ ≤
            MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy c := hrate
        _ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy 0 := by
          simpa using sub_le_self (MetricCodes.binaryEntropy a) hentropy
    · exact binaryRate_le_of_positive_feasible_bound
        hfeasible hpositive (hbound hfeasible hpositive)
  unfold variationalRate
  apply le_csInf (rateSet_nonempty_of_interior hδ hδ')
  rintro _ ⟨a, b, hfeasible, rfl⟩
  exact hcandidate hfeasible
end MetricCodes.Hamming
