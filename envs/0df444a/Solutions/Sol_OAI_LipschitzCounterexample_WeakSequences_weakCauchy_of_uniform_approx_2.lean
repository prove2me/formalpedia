-- Prove2me | solution 2 for OAI.LipschitzCounterexample.WeakSequences.weakCauchy_of_uniform_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:05:07.073322+00:00
-- url     : https://prove2.me/submissions/99a31bc0-5110-47e7-b0bb-03a93d5fae61

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WeakCauchy.lean:L26-L46
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeakSequences.weakCauchy_of_uniform_approx. The node keeps its source
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

theorem weakCauchy_of_uniform_approx {u : ℕ → E}
    (h : ∀ ε : ℝ, 0 < ε → ∃ v : ℕ → E, WeakCauchy v ∧ ∀ i, ‖u i-v i‖ < ε) :
    WeakCauchy u := by
  intro f
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨v,hv,herr⟩ := h (ε/(4*(‖f‖+1))) (by positivity)
  have hferr (i : ℕ) : dist (f (u i)) (f (v i)) < ε/4 := by
    rw [dist_eq_norm,← map_sub]
    have hh := (lt_div_iff₀ (show 0 < 4*(‖f‖+1) by positivity)).mp (herr i)
    have hb := f.le_opNorm (u i-v i)
    nlinarith [norm_nonneg (u i-v i)]
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hv f) (ε/2) (half_pos hε)
  refine ⟨N,fun m hm n hn => ?_⟩
  have h₁ := dist_triangle (f (u m)) (f (v m)) (f (u n))
  have h₂ := dist_triangle (f (v m)) (f (v n)) (f (u n))
  have h₃ := hferr m
  have h₄ := hferr n
  have h₅ := hN m hm n hn
  rw [dist_comm (f (v n)) (f (u n))] at h₂
  linarith

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.LocalizedLinearization
open scoped Topology NNReal
open Filter WeakSequences
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open Filter Topology


theorem solution.{uE} : type_of% @_root_.OAI.LipschitzCounterexample.WeakSequences.weakCauchy_of_uniform_approx.{uE} := @_root_.OAI.LipschitzCounterexample.WeakSequences.weakCauchy_of_uniform_approx.{uE}
