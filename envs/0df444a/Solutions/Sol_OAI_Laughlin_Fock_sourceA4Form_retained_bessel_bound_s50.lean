-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceA4Form_retained_bessel_bound_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:50:17.852508+00:00
-- url     : https://prove2.me/submissions/2a2adaa6-5bca-4d08-ae74-bfee575fe2cd

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020
import Theorems.Thm_OAI_Laughlin_Fock_fourCopyMiddleForm_s50
import Theorems.Thm_OAI_Laughlin_Fock_linearMap_rotation_norm_integrable_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_fourBody_haar_transfer_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_fourBody_total_bessel_haar_allowance_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_fourCopyOperator_haar_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourceA4Form_retained_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

theorem occupationNormSq_nonneg (Q : ℕ) (x : Space Q) : 0 ≤ occupationNormSq Q x := by
  unfold occupationNormSq
  positivity

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_LocalMetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem localMetricError_nonneg (L Q : ℕ) : 0 ≤ localMetricError L Q := norm_nonneg _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_self (Q : ℕ) (x : Space Q) :
    occupationInner Q x x = (occupationNormSq Q x : ℂ) := by
  unfold occupationInner occupationNormSq
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_sum {I J : Type*} [Fintype I] [Fintype J] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (∑ j, M j) x = ∑ j, contractionForm Q minus (M j) x := by
  simp only [contractionForm,Matrix.sum_apply,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_MatrixMetricError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem entrySum_nonneg {I : Type*} [Fintype I] (R : I → I → ℝ) : 0 ≤ entrySum R := by
  unfold entrySum
  positivity

theorem matrixMetricError_nonneg {I : Type*} [Fintype I] (L Q : ℕ) (R S : I → I → ℝ) :
    0 ≤ matrixMetricError L Q R S :=
  add_nonneg (entrySum_nonneg _) (mul_nonneg (localMetricError_nonneg L Q) (entrySum_nonneg R))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TransferCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

theorem fourBodyRho_nonneg (D Q : ℕ) : 0 ≤ fourBodyRho D Q :=
  mul_nonneg (matrixMetricError_nonneg _ _ _ _) (sq_nonneg _)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CopyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem fourCopyOperator_diagonal (Q D : ℕ) (hQ : D+2 ≤ Q) (c : OddPairLabel D → ℝ) :
    fourCopyOperator Q D hQ (Matrix.diagonal c) = ∑ r,
      (c r : ℂ) • (retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ r)ᴴ) := by
  classical
  simp [fourCopyOperator,Matrix.diagonal_apply,apply_ite,ite_smul]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CopyFormAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

private theorem scaled_sum_of_haar_identity {ι : Type*} [Fintype ι]
    (a d t : ℝ) (f : ι → ℝ) (hd : d ≠ 0) (h : d * ∑ i, f i = t) :
    (a / d) * t = ∑ i, a * f i := by
  rw [← h, ← Finset.mul_sum]
  field_simp

theorem fourCopyForm_allowance_identity (Q D : ℕ) (hQ : D+2 ≤ Q) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (∑ r : OddPairLabel D, (contractionForm Q (sourceFourFamilyEnd Q)
        (retainedFourInclusion Q D hQ r*(retainedFourInclusion Q D hQ r)ᴴ) x).re) =
      ∑ r : OddPairLabel D, ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, occupationNormSq Q
        (physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
          (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  classical
  have hd : ((4*Q-1-2*D : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  have h := physical_fourCopyOperator_haar_s50 Q D hQ (Matrix.diagonal (fun _ : OddPairLabel D => (1 : ℝ))) x
  rw [fourCopyOperator_diagonal] at h
  simp only [Complex.ofReal_one,one_smul,contractionForm_sum,Complex.re_sum] at h
  have he (g : SourceSU2) : occupationQuadratic Q (Matrix.diagonal (fun _ : OddPairLabel D => (1 : ℝ)))
      (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) (exteriorRotation Q g⁻¹ x)) =
      ∑ r : OddPairLabel D, occupationNormSq Q
        (physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) (exteriorRotation Q g⁻¹ x)) := by
    simp only [occupationQuadratic,Matrix.diagonal_apply,apply_ite,Complex.ofReal_one,
      Complex.ofReal_zero,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,
      ite_true,occupationInner_self,Complex.re_sum,Complex.ofReal_re]
  simp_rw [he] at h
  rw [integral_finsetSum _ (fun (r : OddPairLabel D) hr => linearMap_rotation_norm_integrable_s50 Q
    (physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)) x)] at h
  exact scaled_sum_of_haar_identity _ _ _ _ hd h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TotalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators

theorem physical_fourBody_total_haar_transfer (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    -(averagedFourTransferError Q * sourceFockEnergy Q x) ≤
      ∑ d : Fin 23, (2*Q-2+1 : ℕ) * (∫ g, occupationQuadratic Q (finiteFourMiddle Q (d.val+1))
        (fun i : Fin ((d.val+2)/2) => physicalFourCopyEnd Q
          (Certificate.copyLabel (D := d.val+1) i) (d.val+1) (by omega)
          (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  have hs : (∑ d : Fin 23, fourBodyRho (d.val+1) Q) ≤ uniformFourBodyRho Q := by
    rw [Fin.sum_univ_eq_sum_range (fun d => fourBodyRho (d+1) Q) 23]
    unfold uniformFourBodyRho
    rw [Finset.sum_range_succ' (fun D => fourBodyRho D Q) 23]
    exact le_add_of_nonneg_right (fourBodyRho_nonneg 0 Q)
  have hE : 0 ≤ sourceFockEnergy Q x :=
    Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  calc
    _ ≤ -(24 * (∑ d : Fin 23, fourBodyRho (d.val+1) Q) * sourceFockEnergy Q x) :=
      neg_le_neg (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hE)
    _ = ∑ d : Fin 23, -(24 * fourBodyRho (d.val+1) Q * sourceFockEnergy Q x) := by
      rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_neg_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      exact physical_fourBody_haar_transfer_s50 Q (d.val+1) hQ (by omega) (by omega) x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

theorem fourCopyForm_scaled_haar (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C : OddPairLabel D → OddPairLabel D → ℝ) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x).re =
    ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, occupationQuadratic Q C
      (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
        (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  rw [← physical_fourCopyOperator_haar_s50 Q D hQ C x]
  have hd : ((4*Q-1-2*D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  field_simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_BesselAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators

theorem retainedFourAllowance_bessel_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    retainedFourAllowance Q hQ x ≤ 1222*sourceFockEnergy Q x := by
  unfold retainedFourAllowance
  simp_rw [fourCopyForm_allowance_identity]
  exact physical_fourBody_total_bessel_haar_allowance_s50 Q hQ x

theorem sourceA4Form_retained_bessel_bound_s50_oai (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤ retainedFourTarget Q hQ x +
      (1222*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  have ht := physical_fourBody_total_haar_transfer Q hQ x
  have ha := retainedFourAllowance_bessel_bound Q hQ x
  have he : (∑ d : Fin 23,
      (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*(d.val+1) : ℕ) : ℝ)) *
        (contractionForm Q (sourceFourFamilyEnd Q)
          (fourCopyOperator Q (d.val+1) (by omega) (finiteFourMiddle Q (d.val+1))) x).re) =
      retainedFourTarget Q hQ x+(3/10^6 : ℝ)*retainedFourAllowance Q hQ x-sourceA4Form Q x := by
    conv_lhs => arg 2; ext d; erw [fourCopyMiddleForm_s50 Q _ (by omega) (by omega) x]
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sourceA4Form_retained_s50 Q hQ x]
    unfold retainedFourTarget retainedFourAllowance
    rw [Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hi : -(averagedFourTransferError Q*sourceFockEnergy Q x) ≤
      retainedFourTarget Q hQ x+(3/10^6 : ℝ)*retainedFourAllowance Q hQ x-sourceA4Form Q x := by
    rw [← he]
    conv_rhs => arg 2; ext d; erw [fourCopyForm_scaled_haar]
    exact ht
  nlinarith

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceA4Form_retained_bessel_bound_s50_oai := @OAI.Laughlin.Fock.sourceA4Form_retained_bessel_bound_s50_oai
