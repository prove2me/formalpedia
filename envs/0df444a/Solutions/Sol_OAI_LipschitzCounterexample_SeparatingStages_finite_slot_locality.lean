-- Prove2me | solution 1 for OAI.LipschitzCounterexample.SeparatingStages.finite_slot_locality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:18:51.379502+00:00
-- url     : https://prove2.me/submissions/92f35533-104b-4db2-90ae-8145fc250377

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/LocalOrthogonality.lean:L170-L208
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.SeparatingStages.finite_slot_locality. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_LipschitzCounterexample_SeparatingStages_pair_slot_locality

-- ---- from OAI.Analysis.LipschitzEquivalence.LocalOrthogonality ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

theorem finite_slot_locality {I : Type uI} [Fintype I] (x : I → M) (hx : Function.Injective x) :
    ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, ∀ i j : I, i ≠ j → ∀ n ≥ l,
      ∀ s ∈ Metric.ball (x i) r, ∀ t ∈ Metric.ball (x j) r,
      ∀ a : BlockLabel n, slot n s a = 0 ∨ slot n t a = 0 := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    let := h
    exact ⟨1,by norm_num,0,fun i => isEmptyElim i⟩
  | inr h =>
    let := h
    have hp : ∀ i j : I, ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, i ≠ j → ∀ n ≥ l,
        ∀ s ∈ Metric.ball (x i) r, ∀ t ∈ Metric.ball (x j) r,
        ∀ a : BlockLabel n, slot n s a = 0 ∨ slot n t a = 0 := by
      intro i j
      by_cases hij : i = j
      · exact ⟨1,by norm_num,0,fun hn => (hn hij).elim⟩
      · obtain ⟨r,hr,l,hl⟩ := pair_slot_locality (show x i ≠ x j from fun he => hij (hx he))
        exact ⟨r,hr,l,fun _ => hl⟩
    choose r hr l hl using hp
    let R := Finset.univ.inf' Finset.univ_nonempty (fun i =>
      Finset.univ.inf' Finset.univ_nonempty (r i))
    let L := Finset.univ.sup (fun i => Finset.univ.sup (l i))
    have hR : 0 < R := by
      apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
      intro i hi
      exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j hj => hr i j)
    have hRle : ∀ i j, R ≤ r i j := by
      intro i j
      exact (Finset.inf'_le _ (Finset.mem_univ i)).trans
        (Finset.inf'_le _ (Finset.mem_univ j))
    have hL : ∀ i j, l i j ≤ L := by
      intro i j
      exact (Finset.le_sup (f := l i) (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun i => Finset.univ.sup (l i)) (Finset.mem_univ i))
    refine ⟨R,hR,L,?_⟩
    intro i j hij n hn s hs t ht a
    exact hl i j hij n ((hL i j).trans hn) s
      (Metric.ball_subset_ball (hRle i j) hs) t (Metric.ball_subset_ball (hRle i j) ht) a

end LipschitzCounterexample.SeparatingStages

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set


theorem solution.{uI} : type_of% @_root_.OAI.LipschitzCounterexample.SeparatingStages.finite_slot_locality.{uI} := @_root_.OAI.LipschitzCounterexample.SeparatingStages.finite_slot_locality.{uI}
