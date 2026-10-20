-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.prefix_radius_approx
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:37:45.699978+00:00
-- url     : https://prove2.me/submissions/9e14712c-aad6-4a69-a631-3b5a65ef3b17

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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
universe uM uE
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]
theorem h50b_supported_mono {K L : Set M} (h : K ⊆ L) : supported K ≤ supported L :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono h))

theorem h50b_approx_ball (μ : Space M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, Approximable μ (Metric.closedBall 0 R) ε := by
  classical
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp dense_combinations μ ε hε
  obtain ⟨R, hR⟩ := (a.support.finite_toSet.isBounded).subset_closedBall (0 : M)
  refine ⟨R, Finsupp.linearCombination ℝ point a, ?_, ?_⟩
  · apply Submodule.le_topologicalClosure
    rw [Finsupp.mem_span_image_iff_linearCombination]
    exact ⟨a, (Finsupp.mem_supported ℝ a).mpr hR, rfl⟩
  · rw [← dist_eq_norm]; exact ha

theorem h50b_approx_mono {μ : Space M} {K L : Set M} {ε : ℝ} (h : K ⊆ L)
    (hK : Approximable μ K ε) : Approximable μ L ε := by
  obtain ⟨ν, hν, hd⟩ := hK
  exact ⟨ν, h50b_supported_mono h hν, hd⟩

theorem solution (μ : ℕ → Space M) {ε : ℝ} (hε : 0 < ε)
    (N : ℕ) (r : ℝ) : ∃ R : ℝ, r ≤ R ∧ 0 < R ∧
      ∀ i < N, Approximable (μ i) (Metric.closedBall 0 R) ε := by
  choose R hR using fun i => h50b_approx_ball (μ i) hε
  refine ⟨|r| + 1 + ∑ i ∈ Finset.range N, |R i|, ?_, ?_, ?_⟩
  · have : 0 ≤ ∑ i ∈ Finset.range N, |R i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith [le_abs_self r]
  · have : 0 ≤ ∑ i ∈ Finset.range N, |R i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith [abs_nonneg r]
  · intro i hi
    apply h50b_approx_mono _ (hR i)
    apply Metric.closedBall_subset_closedBall
    have h1 : |R i| ≤ ∑ j ∈ Finset.range N, |R j| :=
      Finset.single_le_sum (f := fun j => |R j|) (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hi)
    linarith [le_abs_self (R i), abs_nonneg r]

