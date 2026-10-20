-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.uniform_radius_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:49:12.612131+00:00
-- url     : https://prove2.me/submissions/9a1286cd-e169-4be9-a57e-028378e1d915

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/RadiusReduction.lean:L71-L117
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.uniform_radius_approx. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_radius_escape_step
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

-- ---- from OAI.Analysis.LipschitzEquivalence.RadiusReduction ----
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

theorem uniform_radius_approx {μ : ℕ → Space M} (hw : WeakSequences.WeakNull μ)
    {ε : ℝ} (hε : 0 < ε) : ∃ R : ℝ, 0 < R ∧
      ∀ i, Approximable (μ i) (Metric.closedBall 0 R) ε := by
  classical
  by_contra h
  have hfail : ∀ R : ℝ, 0 < R → ∃ i, ¬ Approximable (μ i) (Metric.closedBall 0 R) ε := by
    intro R hR
    by_contra! h'
    exact h ⟨R,hR,h'⟩
  choose idx rad g hip hrad hg hg0 hinner houter hlarge using radius_escape_step hε hfail
  let seq : ℕ → ℕ × ℝ := fun n => Nat.rec (0,1) (fun _ q => (idx q.1 q.2,rad q.1 q.2)) n
  have hs (n : ℕ) : seq (n+1) = (idx (seq n).1 (seq n).2,rad (seq n).1 (seq n).2) := rfl
  have hidx : StrictMono (fun n => (seq n).1) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact hip _ _
  have hradius : StrictMono (fun n => (seq n).2) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact hrad _ _
  let tests : ℕ → M → ℝ := fun n => g (seq n).1 (seq n).2
  have htests (n : ℕ) : LipschitzWith 3 (tests n) := hg _ _
  have hd : DisjointTests tests := by
    intro x j k hj hk
    by_contra hjk
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · have hlow : (seq k).2 < dist x 0 := by
        by_contra hx
        exact hk (hinner _ _ x (le_of_not_gt hx))
      have hupp : dist x 0 < (seq (j+1)).2 := by
        by_contra hx
        exact hj (houter _ _ x (le_of_not_gt hx))
      exact (not_lt_of_ge (hradius.monotone (Nat.succ_le_of_lt hjk))) (hlow.trans hupp)
    · have hlow : (seq j).2 < dist x 0 := by
        by_contra hx
        exact hj (hinner _ _ x (le_of_not_gt hx))
      have hupp : dist x 0 < (seq (k+1)).2 := by
        by_contra hx
        exact hk (houter _ _ x (le_of_not_gt hx))
      exact (not_lt_of_ge (hradius.monotone (Nat.succ_le_of_lt hkj))) (hlow.trans hupp)
  have hw' := hw.subseq (show StrictMono (fun n => (seq (n+1)).1) from
    fun _ _ hnk => hidx (Nat.add_lt_add_right hnk 1))
  have ht := disjoint_tests_vanish hd htests hw'
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/2) (half_pos hε)
  have hn := hN N le_rfl
  simp only [dist_zero_right,Real.norm_eq_abs] at hn
  exact (not_lt_of_gt (hlarge (seq N).1 (seq N).2 (htests N))) hn

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


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.uniform_radius_approx.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.uniform_radius_approx.{uM}
