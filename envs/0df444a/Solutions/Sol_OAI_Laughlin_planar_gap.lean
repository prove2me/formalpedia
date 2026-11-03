-- Prove2me | solution 1 for OAI.Laughlin.planar_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:00:37.749678+00:00
-- url     : https://prove2.me/submissions/550548a9-3e22-4a9d-9438-69acaa475d25

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020
import Theorems.Thm_OAI_Laughlin_Fock_finiteLocalFourMatrix_tendsto_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_fock_sharp_budget_eventually_s50
import Theorems.Thm_OAI_Laughlin_Planar_finite_degree_endpoint_of_fock_square_s50
import Theorems.Thm_OAI_Laughlin_sharp_scalar_budget_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FactorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter

theorem modeFactor_sq_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x)
      atTop (𝓝 1) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range x, (1/1 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(i : ℝ)) 0 1 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x) := by
    filter_upwards [eventually_ge_atTop x] with Q hQ
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : (Q : ℝ)^x = ∏ _i ∈ Finset.range x, (Q : ℝ) := by simp
    rw [hd, ← Finset.prod_div_distrib]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ Q)]
      congr 1 <;> ring
  simpa using hp.congr' he

theorem modeFactor_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => modeFactor Q x) atTop (𝓝 1) := by
  simpa [modeFactor] using (modeFactor_sq_tendsto x).sqrt

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_LocalDiagonalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem localDiagonals_tendsto (L : ℕ) :
    Tendsto (localDiagonals L) atTop (𝓝 (fun _ => (1 : ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro A
  have h : Tendsto (fun Q => ∏ i ∈ A, modeFactor Q i.val) atTop (𝓝 (∏ _i ∈ A, (1 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact modeFactor_tendsto i.val
  simpa [localDiagonals] using h

theorem localInverseDiagonals_tendsto (L : ℕ) :
    Tendsto (fun Q => fun A : Finset (Fin (L+1)) => (localDiagonals L Q A)⁻¹)
      atTop (𝓝 (fun _ => (1 : ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro A
  simpa using ((tendsto_pi_nhds.mp (localDiagonals_tendsto L)) A).inv₀ (by norm_num)

theorem localMetricDiagonals_tendsto (L : ℕ) :
    Tendsto (fun Q => fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2)
      atTop (𝓝 (fun _ => (1 : ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro A
  simpa using ((tendsto_pi_nhds.mp (localInverseDiagonals_tendsto L)) A).pow 2

end Laughlin.Fock

end OAI
end

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

theorem localMetricError_tendsto (L : ℕ) :
    Tendsto (localMetricError L) atTop (𝓝 0) := by
  have h := ((localMetricDiagonals_tendsto L).sub
    (tendsto_const_nhds (x := fun _ : Finset (Fin (L+1)) => (1 : ℝ)))).norm
  change Tendsto (fun Q : ℕ => ‖(fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2) -
    (fun _ : Finset (Fin (L+1)) => (1 : ℝ))‖) atTop (𝓝 0)
  simpa only [sub_self,norm_zero] using h

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

theorem entrySum_tendsto {I : Type*} [Fintype I] (R : ℕ → I → I → ℝ) (S : I → I → ℝ)
    (hR : ∀ i j, Tendsto (fun Q => R Q i j) atTop (𝓝 (S i j))) :
    Tendsto (fun Q => entrySum (R Q)) atTop (𝓝 (entrySum S)) := by
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact (hR i j).abs

theorem matrixMetricError_tendsto {I : Type*} [Fintype I] (L : ℕ)
    (R : ℕ → I → I → ℝ) (S : I → I → ℝ)
    (hR : ∀ i j, Tendsto (fun Q => R Q i j) atTop (𝓝 (S i j))) :
    Tendsto (fun Q => matrixMetricError L Q (R Q) S) atTop (𝓝 0) := by
  have hd := entrySum_tendsto (fun Q i j => R Q i j-S i j) (fun _ _ => 0)
    (fun i j => by simpa using (hR i j).sub_const (S i j))
  have hr := entrySum_tendsto R S hR
  have h := hd.add ((localMetricError_tendsto L).mul hr)
  simpa [matrixMetricError,entrySum] using h

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

theorem fourBodyRho_tendsto (D : ℕ) : Tendsto (fourBodyRho D) atTop (𝓝 0) := by
  have h := (matrixMetricError_tendsto 24 (fun Q => finiteLocalFourMatrix Q D)
    (limitLocalFourMatrix D) (finiteLocalFourMatrix_tendsto_s50 D)).mul_const
      ((Fintype.card (LocalFourIndex D) : ℝ)^2)
  change Tendsto (fun Q => matrixMetricError 24 Q (finiteLocalFourMatrix Q D)
    (limitLocalFourMatrix D) * (Fintype.card (LocalFourIndex D) : ℝ)^2) atTop (𝓝 0)
  simpa using h

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

theorem uniformFourBodyRho_tendsto : Tendsto uniformFourBodyRho atTop (𝓝 0) := by
  have h := tendsto_finsetSum (s := Finset.range 24) (fun D hD => fourBodyRho_tendsto D)
  change Tendsto (fun Q => ∑ D ∈ Finset.range 24, fourBodyRho D Q) atTop (𝓝 0)
  simpa using h

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

theorem averagedFourTransferError_tendsto :
    Filter.Tendsto averagedFourTransferError Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun Q => 24 * uniformFourBodyRho Q) Filter.atTop (𝓝 0)
  simpa only [mul_zero] using uniformFourBodyRho_tendsto.const_mul 24

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_SevenSquareAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem sourceKForm_nonneg (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) : 0 ≤ sourceKForm Q hQ x := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro g
  apply List.sum_nonneg
  intro a ha
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp ha
  exact occupationNormSq_nonneg Q _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_SharpGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open Filter
open scoped Topology BigOperators

theorem one_twenty_fifth_lt_gammaStar : (1/25 : ℝ) < gammaStar := by
  norm_num [gammaStar]

namespace Fock

theorem physical_fock_square_eventually_sharp (γ : ℝ) (hγ : γ < gammaStar) :
    ∀ᶠ Q : ℕ in atTop, ∀ x : Space Q,
      γ*sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  filter_upwards [physical_fock_sharp_budget_eventually_s50,
    sharp_scalar_budget_s50 averagedFourTransferError averagedFourTransferError_tendsto γ hγ]
    with Q h hs
  obtain ⟨hQ,h⟩ := h
  intro x
  have hE : 0 ≤ sourceFockEnergy Q x := Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  have hm := mul_le_mul_of_nonneg_right hs hE
  have hk := sourceKForm_nonneg Q (by omega) x
  have hx := h x
  linarith

end Fock
end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Planar_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Planar
open Fock Filter
open scoped BigOperators Topology Matrix

theorem finite_degree_endpoint (L : ℕ) (x : Space L) (hx : DegreeAtMost L L x) :
    gammaStar * pairEnergy L (planarPairMatrix L) (fun A => (occupationBasis L).repr x A) ≤
      squareNorm L (planarHamiltonian L) (fun A => (occupationBasis L).repr x A) := by
  apply finite_degree_endpoint_of_fock_square_s50 gammaStar
    (lt_trans (by norm_num : (0 : ℝ) < 1/25) one_twenty_fifth_lt_gammaStar)
    (fun γ _hγ hγstar => physical_fock_square_eventually_sharp γ hγstar) L x hx

end Laughlin.Planar

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Planar_Forms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Planar
open Fock
open scoped BigOperators ENNReal

theorem full_planar_endpoint {N : ℕ} (ψ : HomogeneousState N) :
    ENNReal.ofReal gammaStar * fullEnergy ψ ≤ fullSquareNorm ψ := by
  unfold fullEnergy fullSquareNorm
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro L
  have hd : DegreeAtMost L L (ψ.block L) := by
    intro A hA
    exact ψ.homogeneous L A (Or.inr (ne_of_gt hA))
  have h := finite_degree_endpoint L (ψ.block L) hd
  have hγ : 0 ≤ gammaStar :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1/25) one_twenty_fifth_lt_gammaStar)
  rw [← ENNReal.ofReal_mul hγ]
  exact ENNReal.ofReal_le_ofReal h

end Laughlin.Planar

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_UniformGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open Fock

theorem planar_gap_oai {N : ℕ} (ψ : Planar.HomogeneousState N) :
    ENNReal.ofReal gammaStar * Planar.fullEnergy ψ≤Planar.fullSquareNorm ψ :=
  Planar.full_planar_endpoint ψ

end Laughlin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.planar_gap_oai := @OAI.Laughlin.planar_gap_oai
