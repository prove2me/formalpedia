-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CoordinateSpaces.sum_projection_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:30:53.947236+00:00
-- url     : https://prove2.me/submissions/cca9f9f3-12be-4687-ada7-9a5967347f40

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CoordinateSpaces
universe uIndex uI uE uM
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]
theorem h50b_inner_space_zero {S T : Set (Σ n, ι n)} (hST : Disjoint S T) {u v : Hilbert (ι := ι)}
    (hu : u ∈ space S) (hv : v ∈ space T) : ⟪u, v⟫_ℝ = 0 := by
  rw [lp.inner_eq_tsum]
  have : ∀ n, ⟪u n, v n⟫_ℝ = 0 := by
    intro n
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : (⟨n, a⟩ : Σ n, ι n) ∈ S
    · have : v n a = 0 := (mem_space T v).mp hv ⟨n, a⟩ (Set.disjoint_left.mp hST ha)
      simp [this]
    · have : u n a = 0 := (mem_space S u).mp hu ⟨n, a⟩ ha
      simp [this]
  simp [this]

theorem solution {I : Type uI} [Fintype I] (S : I → Set (Σ n, ι n))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (x : Hilbert (ι := ι)) :
    ∑ i, ‖projection (S i) x‖^2 ≤ ‖x‖^2 := by
  classical
  set P : I → Hilbert (ι := ι) := fun i => projection (S i) x with hP
  have hself : ∀ i, ⟪P i, x⟫_ℝ = ‖P i‖ ^ 2 := by
    intro i
    rw [← real_inner_self_eq_norm_sq]
    exact (inner_projection (S i) (projection_mem (S i) x) x).symm
  have horth : ∀ i j, i ≠ j → ⟪P i, P j⟫_ℝ = 0 := fun i j hij =>
    h50b_inner_space_zero (hS hij) (projection_mem _ _) (projection_mem _ _)
  set y := ∑ i, P i with hy
  set s := ∑ i, ‖P i‖ ^ 2 with hs
  have hyx : ⟪y, x⟫_ℝ = s := by
    rw [hy, sum_inner]; exact Finset.sum_congr rfl (fun i _ => hself i)
  have hyy : ‖y‖ ^ 2 = s := by
    rw [← real_inner_self_eq_norm_sq, hy, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum, Finset.sum_eq_single i (fun j _ hji => horth i j (Ne.symm hji)) (by simp)]
    exact real_inner_self_eq_norm_sq _
  have hle : s ≤ ‖y‖ * ‖x‖ := hyx ▸ real_inner_le_norm y x
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hyle : ‖y‖ ≤ ‖x‖ := by
    by_contra hc
    push_neg at hc
    have : ‖y‖ * ‖x‖ < ‖y‖ * ‖y‖ := mul_lt_mul_of_pos_left hc (lt_of_le_of_lt (norm_nonneg _) hc)
    nlinarith
  rw [← hyy]
  exact pow_le_pow_left₀ (norm_nonneg _) hyle 2

