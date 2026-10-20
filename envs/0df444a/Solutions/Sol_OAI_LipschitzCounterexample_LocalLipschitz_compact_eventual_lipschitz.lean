-- Prove2me | solution 1 for OAI.LipschitzCounterexample.LocalLipschitz.compact_eventual_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:28:07.721818+00:00
-- url     : https://prove2.me/submissions/e20cd2ca-cb50-416f-95c5-a75c150aaa47

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalLipschitz
universe uM uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]


theorem solution (R : ℕ → M → ℝ) {K : Set M} (hK : IsCompact K)
    {C : ℝ≥0} (hC : 0 < C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ K, |R i x| < ε)
    (hloc : ∀ p ∈ K, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ᶠ i in atTop, LipschitzOnWith C (R i) (K ∩ V)) :
    ∀ᶠ i in atTop, LipschitzOnWith C (R i) K := by
  choose V hVo hpV hev using hloc
  let c : K → Set M := fun p => V p p.2
  obtain ⟨t, hcov⟩ := hK.elim_finite_subcover c (fun p => hVo p p.2)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpV x hx⟩)
  have hcov' : K ⊆ ⋃ i : t, c i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK (fun i : t => hVo i.1 i.1.2) hcov'
  have hev1 : ∀ᶠ i in atTop, ∀ p ∈ t, LipschitzOnWith C (R i) (K ∩ c p) := by
    rw [Filter.eventually_all_finset]
    intro p _
    exact hev p p.2
  have hCpos : (0 : ℝ) < C := hC
  filter_upwards [hev1, hsmall ((C : ℝ) * δ / 2) (by positivity)] with i h1 h2
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxy : dist y x < δ
  · obtain ⟨p, hp⟩ := hleb x hx
    have hxp : x ∈ c p := hp (Metric.mem_ball_self hδ)
    have hyp : y ∈ c p := hp (Metric.mem_ball.mpr hxy)
    exact (h1 p p.2).dist_le_mul x ⟨hx, hxp⟩ y ⟨hy, hyp⟩
  · push_neg at hxy
    rw [dist_comm] at hxy
    have a1 := h2 x hx
    have a2 := h2 y hy
    rw [Real.dist_eq]
    calc |R i x - R i y| ≤ |R i x| + |R i y| := abs_sub _ _
      _ ≤ (C : ℝ) * δ := by linarith
      _ ≤ C * dist x y := mul_le_mul_of_nonneg_left hxy hCpos.le

