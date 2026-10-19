-- Prove2me | solution 1 for MetricCodes.Boolean.hammingWindowChannelMatrix_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/a592dd45-711b-4c9e-acee-c6a5b4f77546

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentBlockCoefficient_sq_sum
import Theorems.Thm_MetricCodes_Boolean_isLevel_hammingWindowBasis
import Theorems.Thm_MetricCodes_Boolean_dot_hammingWindowBasis
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_isometry
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_orthogonal
import Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
import Theorems.Thm_MetricCodes_Boolean_hammingWindowChannelMatrix_pairing

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v) :
    (hammingWindowChannelMatrix n k L v lam)ᵀ *
      hammingWindowChannelMatrix n k L v lam = 1 := by
  classical
  ext Q R
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [hammingWindowChannelMatrix_pairing]
  rcases Q with ⟨source, S⟩
  rcases R with ⟨other, T⟩
  by_cases heq : source = other
  · subst other
    calc
      (∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target source *
          hammingAdjacentBlockCoefficient n k L v lam target source) *
        coordinateDot
          (hammingAdjacentChannel n k L target source
            (hammingWindowBasis n k L ⟨source, S⟩))
          (hammingAdjacentChannel n k L target source
            (hammingWindowBasis n k L ⟨source, T⟩))) =
        ∑ target : Fin (L - k + 1),
          hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
            dot (hammingWindowBasis n k L ⟨source, S⟩)
              (hammingWindowBasis n k L ⟨source, T⟩) := by
          apply Finset.sum_congr rfl
          intro target _
          by_cases hadjacent : target.val + 1 = source.val ∨
              source.val + 1 = target.val
          · rw [hammingAdjacentChannel_isometry
              hkL hLn target source hadjacent
              (hammingWindowBasis n k L ⟨source, S⟩)
              (hammingWindowBasis n k L ⟨source, T⟩)
              (isLevel_hammingWindowBasis n k L ⟨source, S⟩)]
            ring
          · have hzero :=
              hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
                n k L source target hadjacent
            have hblock :
                hammingAdjacentBlockCoefficient
                  n k L v lam target source = 0 := by
              simp [hammingAdjacentBlockCoefficient, hzero]
            simp [hblock]
      _ = (∑ target : Fin (L - k + 1),
            hammingAdjacentBlockCoefficient n k L v lam target source ^ 2) *
          dot (hammingWindowBasis n k L ⟨source, S⟩)
            (hammingWindowBasis n k L ⟨source, T⟩) := by
          rw [Finset.sum_mul]
      _ = if (⟨source, S⟩ : HammingWindowIndex n k L) =
            (⟨source, T⟩ : HammingWindowIndex n k L)
          then 1 else 0 := by
          rw [hammingAdjacentBlockCoefficient_sq_sum
            hn hkL hLn v hv lam hlam heigen source, one_mul,
            dot_hammingWindowBasis]
          by_cases hST : S = T
          · subst T
            simp
          · have hval : S.val ≠ T.val := by
              intro h
              exact hST (Subtype.ext h)
            have hsigma :
                (⟨source, S⟩ : HammingWindowIndex n k L) ≠
                  (⟨source, T⟩ : HammingWindowIndex n k L) := by
              intro h
              have hsecond : S.val = T.val :=
                congrArg (fun Z : HammingWindowIndex n k L => Z.2.val) h
              exact hval hsecond
            simp [hval, hsigma]
  · have hsigma :
        (⟨source, S⟩ : HammingWindowIndex n k L) ≠
          (⟨other, T⟩ : HammingWindowIndex n k L) := by
      intro h
      exact heq
        (congrArg (fun Z : HammingWindowIndex n k L => Z.1) h)
    rw [if_neg hsigma]
    apply Finset.sum_eq_zero
    intro target _
    rw [hammingAdjacentChannel_orthogonal
      n k L target source other heq
      (hammingWindowBasis n k L ⟨source, S⟩)
      (hammingWindowBasis n k L ⟨other, T⟩)]
    ring
end MetricCodes.Boolean
