-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:52:47.148651+00:00
-- url     : https://prove2.me/submissions/4dbf5f69-a6a6-4c5c-9dc9-56a11e738fe1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/FiniteReduction.lean:L140-L182
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_finite_escape_step
import Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_disjointOperator_coord
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_schur

-- ---- from OAI.Analysis.LipschitzEquivalence.Schur ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem WeakNull.map {u : ℕ → E} (hu : WeakNull u) (T : E →L[ℝ] F) :
    WeakNull (fun n => T (u n)) := fun f => hu (f.comp T)

theorem WeakNull.subseq {u : ℕ → E} (hu : WeakNull u) {a : ℕ → ℕ} (ha : StrictMono a) :
    WeakNull (fun n => u (a n)) := fun f => (hu f).comp ha.tendsto_atTop

end WeakSequences

end LipschitzCounterexample
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.Localization ----
namespace OAI

universe uM uV

noncomputable section
namespace LipschitzCounterexample

namespace LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem disjoint_tests_vanish {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) :
    Tendsto (fun i => test (normalized (h i) (hh i)) (μ i)) atTop (𝓝 0) := by
  have hn := WeakSequences.schur (hw.map (disjointOperator hd))
  apply squeeze_zero_norm (fun i => ?_) (by simpa only [norm_zero] using hn.norm)
  rw [← disjointOperator_coord hd hh]
  exact lp.norm_apply_le_norm (by norm_num) _ _

end LocalizedLinearization

end LipschitzCounterexample
end

end OAI

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

theorem uniform_finite_neighborhood_approx {μ : ℕ → Space M}
    (hw : WeakSequences.WeakNull μ) {R : ℝ≥0}
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
  have ht := disjoint_tests_vanish hd hg hw'
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


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx.{uM}
