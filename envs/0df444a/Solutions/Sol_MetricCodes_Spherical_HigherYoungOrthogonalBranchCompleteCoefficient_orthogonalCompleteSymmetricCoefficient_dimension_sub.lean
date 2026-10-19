-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient.orthogonalCompleteSymmetricCoefficient_dimension_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/68d833ac-f1f3-4a9b-aa5f-6409dfde05a8

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
namespace MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
theorem _root_.solution
    {n : ℕ} (hn : 2 ≤ n) (k : ℤ) :
    orthogonalCompleteSymmetricCoefficient n k -
        orthogonalCompleteSymmetricCoefficient n (k - 1) =
      orthogonalCompleteSymmetricCoefficient (n - 1) k := by
  by_cases hk : 0 ≤ k
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    cases m with
    | zero =>
        simp [orthogonalCompleteSymmetricCoefficient]
    | succ m =>
        have hprev : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
        rw [hprev, orthogonalCompleteSymmetricCoefficient_nat,
          orthogonalCompleteSymmetricCoefficient_nat,
          orthogonalCompleteSymmetricCoefficient_nat]
        have hfirst : n + (m + 1) - 1 = n + m := by omega
        have hthird : n - 1 + (m + 1) - 1 = n + m - 1 := by omega
        rw [hfirst, hthird]
        have hpascal := Nat.choose_succ_succ (n + m - 1) m
        have htop : n + m - 1 + 1 = n + m := by omega
        have hpascal' :
            ((n + m).choose (m + 1) : ℤ) =
              ((n + m - 1).choose m : ℤ) +
                ((n + m - 1).choose (m + 1) : ℤ) := by
          exact_mod_cast (show
            (n + m).choose (m + 1) =
              (n + m - 1).choose m +
                (n + m - 1).choose (m + 1) by
            simpa [Nat.succ_eq_add_one, htop] using hpascal)
        omega
  · have hkneg : k < 0 := lt_of_not_ge hk
    have hkprev : k - 1 < 0 := by omega
    rw [orthogonalCompleteSymmetricCoefficient_of_neg n hkneg,
      orthogonalCompleteSymmetricCoefficient_of_neg n hkprev,
      orthogonalCompleteSymmetricCoefficient_of_neg (n - 1) hkneg]
    rfl
end MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
