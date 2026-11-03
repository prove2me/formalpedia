-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_fourBody_haar_transfer_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:22:00.170092+00:00
-- url     : https://prove2.me/submissions/a021b5aa-a26c-4733-acae-0b46ffd4fd0f

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Fock_limitFourCopyEnd_local_sum_s50
import Theorems.Thm_OAI_Laughlin_Fock_linearMap_rotation_norm_integrable_s50
import Theorems.Thm_OAI_Laughlin_Fock_localFourOperators_bound_s50
import Theorems.Thm_OAI_Laughlin_Fock_occupationQuadratic_factor_s50
import Theorems.Thm_OAI_Laughlin_Fock_occupationQuadratic_rotation_integrable_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_pair_norm_haar_real_s50
import Theorems.Thm_OAI_Laughlin_Fock_source_fourBody_limitpositive_s50
import Theorems.Thm_OAI_Laughlin_Fock_truncatedQuadratic_error_s50
import Theorems.Thm_OAI_Laughlin_Fock_truncated_pair_window_return_s50
import Theorems.Thm_OAI_Laughlin_Fock_truncated_sourceFour_conjugation_s50

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

theorem localMetricError_bound (L Q : ℕ) (A : Finset (Fin (L+1))) :
    |((localDiagonals L Q A)⁻¹)^2-1| ≤ localMetricError L Q := by
  have h := norm_le_pi_norm (fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2-1) A
  change ‖((localDiagonals L Q A)⁻¹)^2-1‖ ≤ localMetricError L Q at h
  rw [Real.norm_eq_abs] at h
  exact h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_TruncatedScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem truncatedDiagonals_local (L Q : ℕ) (hL : L ≤ Q) (A : Finset (Fin (Q+1))) :
    truncatedDiagonals L Q A = localDiagonals L Q (localOccupation L Q hL A) := by
  classical
  unfold truncatedDiagonals truncatedModeFactor localDiagonals
  rw [← Finset.prod_filter]
  symm
  apply Finset.prod_bij (fun i hi => (⟨i.val,by have := i.isLt; omega⟩ : Fin (Q+1)))
  · intro i hi
    simp only [localOccupation,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    exact Finset.mem_filter.mpr ⟨hi,by change i.val ≤ L; have := i.isLt; omega⟩
  · intro i hi j hj he
    exact Fin.ext (congrArg (@Fin.val (Q+1)) he)
  · intro i hi
    obtain ⟨hiA,hiL⟩ := Finset.mem_filter.mp hi
    refine ⟨⟨i.val,by omega⟩,?_,?_⟩
    · simpa [localOccupation] using hiA
    · rfl
  · intro i hi
    rfl

theorem truncatedMetricError_bound (L Q : ℕ) (hL : L ≤ Q) (A : Finset (Fin (Q+1))) :
    |((truncatedDiagonals L Q A)⁻¹)^2-1| ≤ localMetricError L Q := by
  rw [truncatedDiagonals_local L Q hL]
  exact localMetricError_bound L Q _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_OrbitIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators

theorem sourcePairWindow_haar (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (2*Q-2+1 : ℕ) * (∫ g, sourcePairWindow Q (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      24 * sourceFockEnergy Q x := by
  unfold sourcePairWindow
  rw [integral_finsetSum _ (fun p hp => linearMap_rotation_norm_integrable_s50 Q _ x)]
  have hp (p : ℕ) (h : p ∈ Finset.range 24) :
      (∫ g, occupationNormSq Q (sourcePairEnd Q p (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      sourceFockEnergy Q x/(2*Q-2+1 : ℕ) :=
    physical_pair_norm_haar_real_s50 Q (by omega) ⟨p,by simp only [Finset.mem_range] at h; omega⟩ x
  rw [Finset.sum_congr rfl hp]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hd : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

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

theorem abs_le_entrySum {I : Type*} [Fintype I] (R : I → I → ℝ) (i j : I) : |R i j| ≤ entrySum R := by
  apply (Finset.single_le_sum (fun k hk => abs_nonneg (R i k)) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k hk => Finset.sum_nonneg (fun l hl => abs_nonneg (R k l))) (Finset.mem_univ i)

theorem matrixMetricError_nonneg {I : Type*} [Fintype I] (L Q : ℕ) (R S : I → I → ℝ) :
    0 ≤ matrixMetricError L Q R S :=
  add_nonneg (entrySum_nonneg _) (mul_nonneg (localMetricError_nonneg L Q) (entrySum_nonneg R))

theorem matrixMetricError_bound {I : Type*} [Fintype I] (L Q : ℕ) (hL : L ≤ Q)
    (R S : I → I → ℝ) (A : Finset (Fin (Q+1))) (i j : I) :
    |((truncatedDiagonals L Q A)⁻¹)^2*R i j-S i j| ≤ matrixMetricError L Q R S := by
  have he : ((truncatedDiagonals L Q A)⁻¹)^2*R i j-S i j =
      (((truncatedDiagonals L Q A)⁻¹)^2-1)*R i j+(R i j-S i j) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have h₁ := mul_le_mul (truncatedMetricError_bound L Q hL A) (abs_le_entrySum R i j)
    (abs_nonneg _) (localMetricError_nonneg L Q)
  have h₂ := abs_le_entrySum (fun i j => R i j-S i j) i j
  unfold matrixMetricError
  linarith

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_TruncatedFourCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem physicalFourCopyEnd_truncated (Q r D : ℕ) (hDQ : D ≤ Q) (hQ : 24 ≤ Q)
    (hD : D ≤ 23) (x : Space Q) :
    physicalFourCopyEnd Q r D hDQ x = truncatedScalingInv 24 Q
      (∑ b : LocalFourIndex D, (physicalFourBeta Q r D b : ℂ) •
        localFourOperators Q D hDQ b (truncatedScaling 24 Q x)) := by
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,localFourOperators]
  apply Finset.sum_congr rfl
  intro b hb
  rw [truncated_sourceFour_conjugation_s50 24 Q b.val.1.val (by omega) (by omega) (by omega)
    _ _ (by change b.val.2.1.val ≤ 24; omega) (by change b.val.2.2.val ≤ 24; omega)]
  rw [smul_smul]
  congr 1
  simp only [physicalFourBeta]
  push_cast
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_UniformTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

theorem source_fourBody_uniform_transfer (Q D : ℕ) (hQ : 24 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    -(fourBodyRho D Q * sourcePairWindow Q x) ≤
      occupationQuadratic Q (finiteFourMiddle Q D)
        (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D (by omega) x) := by
  let hDQ : D ≤ Q := by omega
  let v : LocalFourIndex D → Space Q := fun b =>
    localFourOperators Q D hDQ b (truncatedScaling 24 Q x)
  let ε := matrixMetricError 24 Q (finiteLocalFourMatrix Q D) (limitLocalFourMatrix D)
  let n : ℝ := Fintype.card (LocalFourIndex D)
  have hε : 0 ≤ ε := matrixMetricError_nonneg _ _ _ _
  have hn : 0 ≤ n := by positivity
  have hfinite : occupationQuadratic Q (finiteFourMiddle Q D)
      (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D hDQ x) =
      occupationQuadratic Q (finiteLocalFourMatrix Q D) (fun b => truncatedScalingInv 24 Q (v b)) := by
    simp_rw [physicalFourCopyEnd_truncated Q _ D hDQ hQ hD₂ x,map_sum,map_smul]
    exact occupationQuadratic_factor_s50 Q (finiteFourMiddle Q D) _ _
  rw [hfinite]
  have hbase := source_fourBody_limitpositive_s50 Q D (by omega) hD₁ hD₂ (truncatedScaling 24 Q x)
  change 0 ≤ occupationQuadratic Q (limitFourMiddle D)
    (fun i => limitFourCopyEnd Q (Certificate.copyLabel i) D (truncatedScaling 24 Q x)) at hbase
  have hends (i : Fin ((D+1)/2)) :
      limitFourCopyEnd Q (Certificate.copyLabel i) D (truncatedScaling 24 Q x) =
        ∑ b : LocalFourIndex D,
          (fourBodyLimitCoefficient (Certificate.copyLabel i) D D
            b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) • v b := by
    apply limitFourCopyEnd_local_sum_s50 Q _ D hDQ
    · unfold Certificate.copyLabel; have := i.isLt; omega
    · exact ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  simp_rw [hends] at hbase
  have hbase := hbase.trans_eq (occupationQuadratic_factor_s50 Q (limitFourMiddle D)
    (fun (i : Fin ((D+1)/2)) (b : LocalFourIndex D) =>
      fourBodyLimitCoefficient (Certificate.copyLabel i) D D b.val.1.val b.val.2.1.val b.val.2.2.val) v)
  change 0 ≤ occupationQuadratic Q (limitLocalFourMatrix D) v at hbase
  have herr := truncatedQuadratic_error_s50 24 Q (finiteLocalFourMatrix Q D)
    (limitLocalFourMatrix D) v ε hε (matrixMetricError_bound 24 Q hQ _ _)
  have hpair : (∑ b, occupationNormSq Q (v b)) ≤ n * sourcePairWindow Q x := by
    apply (localFourOperators_bound_s50 Q D hDQ hD₂ (truncatedScaling 24 Q x)).trans
    exact mul_le_mul_of_nonneg_left (truncated_pair_window_return_s50 Q hQ x) hn
  have hbound : |occupationQuadratic Q (finiteLocalFourMatrix Q D) (fun b => truncatedScalingInv 24 Q (v b)) -
      occupationQuadratic Q (limitLocalFourMatrix D) v| ≤ fourBodyRho D Q * sourcePairWindow Q x := by
    apply herr.trans
    calc
      _ ≤ ε*n*(n*sourcePairWindow Q x) := mul_le_mul_of_nonneg_left hpair (mul_nonneg hε hn)
      _ = _ := by change ε*n*(n*sourcePairWindow Q x)=(ε*n^2)*sourcePairWindow Q x; ring
  have hl := (abs_le.mp hbound).1
  linarith

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_HaarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Topology

theorem physical_fourBody_haar_transfer_s50_oai (Q D : ℕ) (hQ : 25 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    -(24 * fourBodyRho D Q * sourceFockEnergy Q x) ≤
      (2*Q-2+1 : ℕ) * (∫ g, occupationQuadratic Q (finiteFourMiddle Q D)
        (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D
          (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  have hw : Integrable (fun g : SourceSU2 => sourcePairWindow Q (exteriorRotation Q g⁻¹ x)) sourceHaar :=
    integrable_finsetSum _ (fun (p : ℕ) hp =>
      linearMap_rotation_norm_integrable_s50 Q (sourcePairEnd Q p) x)
  let L : Fin ((D+1)/2) → Module.End ℂ (Space Q) := fun i =>
    physicalFourCopyEnd Q (Certificate.copyLabel i) D (by omega)
  have hi := integral_mono ((hw.const_mul (fourBodyRho D Q)).neg)
    (occupationQuadratic_rotation_integrable_s50 Q (finiteFourMiddle Q D) L x)
    (fun g => source_fourBody_uniform_transfer Q D (by omega) hD₁ hD₂ (exteriorRotation Q g⁻¹ x))
  have hi := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2*Q-2+1 : ℕ))
  simp only [Pi.neg_apply] at hi
  rw [integral_neg,integral_const_mul] at hi
  have he : ((2*Q-2+1 : ℕ) : ℝ) *
      -(fourBodyRho D Q * (∫ g, sourcePairWindow Q (exteriorRotation Q g⁻¹ x) ∂sourceHaar)) =
        -(24 * fourBodyRho D Q * sourceFockEnergy Q x) := by
    calc
      _ = -(fourBodyRho D Q * ((2*Q-2+1 : ℕ) *
        (∫ g, sourcePairWindow Q (exteriorRotation Q g⁻¹ x) ∂sourceHaar))) := by ring
      _ = _ := by rw [sourcePairWindow_haar Q hQ]; ring
  rwa [he] at hi

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_fourBody_haar_transfer_s50_oai := @OAI.Laughlin.Fock.physical_fourBody_haar_transfer_s50_oai
