-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.nested_finite_cover_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:56:46.054106+00:00
-- url     : https://prove2.me/submissions/44f82e6b-9ae6-4c86-bda5-c5885ec95031

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompactSupports.lean:L63-L82
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.nested_finite_cover_uniform. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports

-- ---- from OAI.Analysis.LipschitzEquivalence.CompactSupports ----
namespace OAI

universe uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped Topology
open Filter Set
variable {M : Type uM} [MetricSpace M]

theorem nested_finite_cover_range (K : ℕ → Set M) (hanti : Antitone K)
    (A : ℕ → Finset M) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hcover : ∀ n, K (n+1) ⊆ Near (A n) (r n))
    (x : ℕ → M) (hx : ∀ n, x n ∈ K n) : TotallyBounded (Set.range x) := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hr ε hε
  have hrN : r N < ε := (le_abs_self _).trans_lt (by simpa only [dist_zero_right,Real.norm_eq_abs] using hN N le_rfl)
  let F : Finset M := A N ∪ (Finset.range (N+1)).image x
  refine ⟨(F : Set M),F.finite_toSet,?_⟩
  rintro _ ⟨n,rfl⟩
  by_cases hn : n < N+1
  · apply Set.mem_iUnion₂.mpr
    refine ⟨x n,?_,?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hn,rfl⟩)
    · simpa only [Metric.mem_ball,dist_self] using hε
  · obtain ⟨a,ha,hxa⟩ := hcover N (hanti (le_of_not_gt hn) (hx n))
    exact Set.mem_iUnion₂.mpr ⟨a,Finset.mem_union_left _ ha,hxa.trans_lt hrN⟩

theorem nested_finite_cover_uniform [CompleteSpace M] (K : ℕ → Set M)
    (hc : ∀ n, IsClosed (K n)) (hanti : Antitone K)
    (A : ℕ → Finset M) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hcover : ∀ n, K (n+1) ⊆ Near (A n) (r n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ x ∈ K N, ∃ y ∈ ⋂ n, K n, dist x y < ε := by
  classical
  by_contra! h
  choose x hx hfar using h
  have hb := nested_finite_cover_range K hanti A r hr hcover x hx
  have hcompact : IsCompact (closure (Set.range x)) :=
    isCompact_iff_totallyBounded_isComplete.mpr ⟨hb.closure,isClosed_closure.isComplete⟩
  obtain ⟨y,_hy,a,ha,hlim⟩ := hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have hy : y ∈ ⋂ n, K n := by
    apply Set.mem_iInter.mpr
    intro n
    apply (hc n).mem_of_tendsto hlim
    filter_upwards [(tendsto_atTop.mp ha.tendsto_atTop) n] with i hi
    exact hanti hi (hx (a i))
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  exact (not_lt_of_ge (hfar (a N) y hy)) (hN N le_rfl)

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.FreeSpace

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped Topology
open Filter Set


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.nested_finite_cover_uniform.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.nested_finite_cover_uniform.{uM}
