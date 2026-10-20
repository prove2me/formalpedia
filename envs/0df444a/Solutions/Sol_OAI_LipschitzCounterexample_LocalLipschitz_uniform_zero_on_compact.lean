-- Prove2me | solution 1 for OAI.LipschitzCounterexample.LocalLipschitz.uniform_zero_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:22:23.423902+00:00
-- url     : https://prove2.me/submissions/f8275797-4d93-4362-b55c-dda98e88787e

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalLipschitz
universe uM uN uB uIndex
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} [MetricSpace M]


theorem solution (f : ℕ → M → ℝ) {L : ℝ≥0}
    (hf : ∀ i, LipschitzWith L (f i))
    (hpoint : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 0))
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x ∈ K, |f i x| < ε := by
  set c : ℝ := (L : ℝ) + 1 with hc
  have hcpos : 0 < c := by positivity
  have hδ : 0 < ε / (2 * c) := by positivity
  obtain ⟨t, hcov⟩ := hK.elim_finite_subcover (fun y : K => Metric.ball (y : M) (ε / (2 * c)))
    (fun _ => Metric.isOpen_ball) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hδ⟩)
  have hev : ∀ᶠ i in atTop, ∀ y ∈ t, |f i (y : M)| < ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro y _
    have := (hpoint y).eventually (Metric.ball_mem_nhds 0 (by positivity : (0:ℝ) < ε / 2))
    filter_upwards [this] with i hi
    simpa [Real.dist_eq] using hi
  filter_upwards [hev] with i hi x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (hcov hx)
  have h1 := hi y hyt
  have h2 : |f i x - f i y| ≤ L * dist x y := by
    have := (hf i).dist_le_mul x y; rwa [Real.dist_eq] at this
  have h3 : (L : ℝ) * dist x y ≤ c * (ε / (2 * c)) := by
    apply mul_le_mul (by linarith) (Metric.mem_ball.mp hxy).le dist_nonneg hcpos.le
  have h4 : c * (ε / (2 * c)) = ε / 2 := by field_simp
  calc |f i x| = |(f i x - f i y) + f i y| := by ring_nf
    _ ≤ |f i x - f i y| + |f i y| := abs_add_le _ _
    _ < ε := by linarith

