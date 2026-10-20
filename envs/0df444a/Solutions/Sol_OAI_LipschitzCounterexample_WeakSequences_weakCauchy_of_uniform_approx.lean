-- Prove2me | solution 1 for OAI.LipschitzCounterexample.WeakSequences.weakCauchy_of_uniform_approx
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:33:32.896537+00:00
-- url     : https://prove2.me/submissions/9fce9856-ca04-406d-803f-7a7d4a07a2e9

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
universe uE uM
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem solution {u : ℕ → E}
    (h : ∀ ε : ℝ, 0 < ε → ∃ v : ℕ → E, WeakCauchy v ∧ ∀ i, ‖u i-v i‖ < ε) :
    WeakCauchy u := by
  intro f
  rw [Metric.cauchySeq_iff]
  intro e he
  set c : ℝ := ‖f‖ + 1 with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨v, hv, hclose⟩ := h (e / (3 * c)) (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hv f) (e / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 : ∀ k, dist (f (u k)) (f (v k)) ≤ ‖f‖ * (e / (3 * c)) := by
    intro k
    rw [Real.dist_eq, ← map_sub]
    exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hclose k).le (norm_nonneg _))
  have h2 : ‖f‖ * (e / (3 * c)) < e / 3 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg f]
  calc dist (f (u m)) (f (u n)) ≤ dist (f (u m)) (f (v m)) + dist (f (v m)) (f (v n)) + dist (f (v n)) (f (u n)) := dist_triangle4 _ _ _ _
    _ < e / 3 + e / 3 + e / 3 := by
      have := h1 n; rw [dist_comm] at this
      have := hN m hm n hn
      linarith [h1 m]
    _ = e := by ring

