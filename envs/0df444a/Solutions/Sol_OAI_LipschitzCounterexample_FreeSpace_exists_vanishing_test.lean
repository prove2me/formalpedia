-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.exists_vanishing_test
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:40:43.372525+00:00
-- url     : https://prove2.me/submissions/5e946a71-d698-4fe9-a74a-8b1bf78adb32

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
theorem h50b_clm_ext (S T : Space M →L[ℝ] ℝ) (h : ∀ x, S (point x) = T (point x)) : S = T := by
  have hlin : S.toLinearMap ∘ₗ Finsupp.linearCombination ℝ point =
      T.toLinearMap ∘ₗ Finsupp.linearCombination ℝ point := by
    apply Finsupp.lhom_ext
    intro x c
    simp [h x]
  have := dense_combinations.equalizer S.continuous T.continuous (by
    funext a
    exact LinearMap.congr_fun hlin a)
  exact ContinuousLinearMap.coe_injective (by
    ext μ
    exact congrFun this μ)

theorem solution (K : Set M) (μ : Space M) {ε : ℝ}
    (hfar : ∀ ν : Space M, ν ∈ supported K → ε ≤ ‖μ-ν‖) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧ f 0 = 0 ∧ (∀ x ∈ K, f x = 0) ∧
      ∀ hf : LipschitzWith 1 f, ε ≤ test (normalized f hf) μ := by
  by_cases hε : ε ≤ 0
  · refine ⟨fun _ => 0, (LipschitzWith.const 0).weaken (zero_le_one), rfl, fun _ _ => rfl, fun hf => ?_⟩
    have : LocalizedLinearization.test (LocalizedLinearization.normalized (fun _ : M => (0:ℝ)) hf) μ = 0 := by
      change μ.1 _ = 0
      have : LocalizedLinearization.normalized (fun _ : M => (0:ℝ)) hf = 0 := by
        apply Subtype.ext; funext x; change (0:ℝ) - 0 = 0; ring
      rw [this, map_zero]
    rw [this]; exact hε
  push Not at hε
  set W := supported K with hW
  have : IsClosed (W : Set (Space M)) := Submodule.isClosed_topologicalClosure _
  set q : Space M ⧸ W := Submodule.Quotient.mk μ with hq
  have hqnorm : ε ≤ ‖q‖ := by
    apply le_of_forall_pos_lt_add
    intro δ hδ
    obtain ⟨m, hm, hmn⟩ := Submodule.Quotient.norm_mk_lt q hδ
    have hmem : μ - m ∈ W := by
      have := (Submodule.Quotient.eq W).mp (hm.trans hq)
      rw [← neg_mem_iff, neg_sub]; exact this
    have := hfar _ hmem
    rw [sub_sub_cancel] at this
    linarith
  have hq0 : ‖q‖ ≠ 0 := by
    intro h0; rw [h0] at hqnorm; linarith
  obtain ⟨g, hg1, hgq⟩ := exists_dual_vector ℝ q hq0
  set T : Space M →L[ℝ] ℝ := g.comp W.mkQL with hT
  have hTn : ‖T‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    calc ‖T x‖ = ‖g (W.mkQL x)‖ := rfl
      _ ≤ ‖g‖ * ‖W.mkQL x‖ := g.le_opNorm _
      _ ≤ 1 * ‖x‖ := by rw [hg1]; exact mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le W x) zero_le_one
  have hlip : LipschitzWith 1 (fun x => T (point x)) := (dual_point_lipschitz T).weaken hTn
  refine ⟨fun x => T (point x), hlip, by simp, ?_, fun hf => ?_⟩
  · intro x hx
    change g (W.mkQL (point x)) = 0
    have : W.mkQL (point x) = 0 := by
      change Submodule.Quotient.mk (point x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [this, map_zero]
  · have : LocalizedLinearization.test (LocalizedLinearization.normalized _ hf) = T := by
      apply h50b_clm_ext
      intro x
      rw [LocalizedLinearization.test_point]
      change T (point x) - T (point 0) = T (point x)
      simp
    rw [this]
    change ε ≤ g q
    rw [hgq]; exact hqnorm

