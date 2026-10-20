-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:12:52.775166+00:00
-- url     : https://prove2.me/submissions/b018d0fa-3976-488f-9bb5-39910b1df59e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CauchyApproximation.lean:L68-L110
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx_cauchy. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_finite_escape_step
import Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_disjoint_tests_vanish_cauchy

-- ---- from OAI.Analysis.LipschitzEquivalence.FiniteReduction ----
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
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

omit [Zero M] in
theorem near_mono {A B : Finset M} (h : A ⊆ B) (δ : ℝ) : Near A δ ⊆ Near B δ := by
  rintro x ⟨a,ha,hxa⟩
  exact ⟨a,h ha,hxa⟩

end LipschitzCounterexample.FreeSpace

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.WeakCauchy ----
namespace OAI

universe uE uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem WeakCauchy.subseq {u : ℕ → E} (h : WeakCauchy u) {a : ℕ → ℕ}
    (ha : StrictMono a) : WeakCauchy (fun n => u (a n)) :=
  fun f => (h f).comp_tendsto ha.tendsto_atTop

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.LocalizedLinearization
open scoped Topology NNReal
open Filter WeakSequences
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.CauchyApproximation ----
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
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem uniform_finite_neighborhood_approx_cauchy {μ : ℕ → Space M}
    (hw : WeakSequences.WeakCauchy μ) {R : ℝ≥0}
    (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {δ : ℝ≥0} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset M, (0 : M) ∈ A ∧ ∀ i, Approximable (μ i) (Near A δ) ε := by
  classical
  by_contra h
  have hfail : ∀ A : Finset M, (0 : M) ∈ A → ∃ i, ¬ Approximable (μ i) (Near A δ) ε := by
    intro A hA
    by_contra! h'
    exact h ⟨A,hA,h'⟩
  choose idx pts tests hip hpts hequi hz hinner houter hlarge using
    finite_escape_step hε hsupp hδ hfail
  let seq : ℕ → ℕ × Finset M := fun n =>
    Nat.rec (0,{0}) (fun _ q => (idx q.1 q.2,q.2 ∪ pts q.1 q.2)) n
  have hidx : StrictMono (fun n => (seq n).1) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact hip _ _
  have hsets : Monotone (fun n => (seq n).2) := by
    apply monotone_nat_of_le_succ
    intro n
    exact Finset.subset_union_left
  let g : ℕ → M → ℝ := fun n => tests (seq n).1 (seq n).2
  have hg (n : ℕ) : LipschitzWith (3+(2/δ)*(2*R+2)) (g n) := hequi _ _
  have hexcl (j k : ℕ) (hjk : j < k) (x : M) (hj : g j x ≠ 0) : g k x = 0 := by
    have hx := houter (seq j).1 (seq j).2 x hj
    apply hinner
    apply near_mono (hsets (Nat.succ_le_of_lt hjk)) _
    exact near_mono Finset.subset_union_right _ hx
  have hd : DisjointTests g := by
    intro x j k hj hk
    by_contra hjk
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · exact hk (hexcl j k hjk x hj)
    · exact hj (hexcl k j hkj x hk)
  have hw' := hw.subseq (show StrictMono (fun n => (seq (n+1)).1) from
    fun _ _ hnk => hidx (Nat.add_lt_add_right hnk 1))
  have ht := disjoint_tests_vanish_cauchy hd hg hw'
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/2) (half_pos hε)
  have hn := hN N le_rfl
  simp only [dist_zero_right,Real.norm_eq_abs] at hn
  exact (not_lt_of_gt (hlarge (seq N).1 (seq N).2 (hg N))) hn

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
open scoped NNReal Topology
open Filter Set LocalizedLinearization


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx_cauchy.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx_cauchy.{uM}
