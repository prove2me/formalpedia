-- Prove2me | solution 2 for OAI.LipschitzCounterexample.LocalLipschitz.compact_eventual_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:30:50.722008+00:00
-- url     : https://prove2.me/submissions/b3f08fcf-577f-4e17-b9d9-f90e0b70a096

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompactLipschitz.lean:L69-L102
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.LocalLipschitz.compact_eventual_lipschitz. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz

-- ---- from OAI.Analysis.LipschitzEquivalence.CompactLipschitz ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uM uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem compact_eventual_lipschitz (R : ℕ → M → ℝ) {K : Set M} (hK : IsCompact K)
    {C : ℝ≥0} (hC : 0 < C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ K, |R i x| < ε)
    (hloc : ∀ p ∈ K, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ᶠ i in atTop, LipschitzOnWith C (R i) (K ∩ V)) :
    ∀ᶠ i in atTop, LipschitzOnWith C (R i) K := by
  classical
  choose V hV hpV hlocV using fun p : K => hloc p.1 p.2
  have hcover : K ⊆ ⋃ p : K, V p := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hpV ⟨x,hx⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV hcover
  have hcover' : K ⊆ ⋃ p : s, V p.1 := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨⟨p,hp⟩,hxp⟩
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric hK (fun p : s => hV p.1) hcover'
  have hall : ∀ᶠ i in atTop, ∀ p : s, LipschitzOnWith C (R i) (K ∩ V p.1) :=
    Filter.eventually_all.mpr (fun p => hlocV p.1)
  have hC' : 0 < (C : ℝ) := hC
  have hsml := hsmall ((C : ℝ)*δ/2) (by positivity)
  filter_upwards [hall,hsml] with i hi hsi
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxy : dist x y < δ
  · obtain ⟨p,hp⟩ := hLeb x hx
    exact (hi p).dist_le_mul x ⟨hx,hp (Metric.mem_ball_self hδ)⟩ y
      ⟨hy,hp (by simpa only [Metric.mem_ball,dist_comm] using hxy)⟩
  · have htri := abs_sub (R i x) (R i y)
    have hxsmall := hsi x hx
    have hysmall := hsi y hy
    rw [Real.dist_eq]
    have hd : δ ≤ dist x y := le_of_not_gt hxy
    nlinarith [mul_le_mul_of_nonneg_left hd hC'.le]
end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

end LipschitzCounterexample.LocalGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalLipschitz
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.LocalLipschitz.compact_eventual_lipschitz.{uM} := @_root_.OAI.LipschitzCounterexample.LocalLipschitz.compact_eventual_lipschitz.{uM}
