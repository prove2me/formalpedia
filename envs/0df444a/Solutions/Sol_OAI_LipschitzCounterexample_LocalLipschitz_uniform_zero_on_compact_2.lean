-- Prove2me | solution 2 for OAI.LipschitzCounterexample.LocalLipschitz.uniform_zero_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:25:56.514408+00:00
-- url     : https://prove2.me/submissions/804f9051-cf8a-4bc8-b816-b38d30691197

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/LocalLipschitz.lean:L80-L106
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.LocalLipschitz.uniform_zero_on_compact. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzEquivalence.LocalLipschitz ----
namespace OAI

universe uM uN uB uIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {N : Type uN} [MetricSpace M] [MetricSpace N]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} [MetricSpace M]

theorem uniform_zero_on_compact (f : ℕ → M → ℝ) {L : ℝ≥0}
    (hf : ∀ i, LipschitzWith L (f i))
    (hpoint : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 0))
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x ∈ K, |f i x| < ε := by
  classical
  let δ : ℝ := ε / (2 * ((L : ℝ)+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t,ht,hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded δ hδ
  let : Fintype t := ht.fintype
  have hsmall : ∀ᶠ i in atTop, ∀ y : t, |f i y| < ε/2 := by
    apply Filter.eventually_all.mpr
    intro y
    have hlim := (hpoint y.val).abs
    simp only [abs_zero] at hlim
    exact hlim.eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [hsmall] with i hi x hx
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hdist : dist x y < δ := hxy
  have hLip := (hf i).dist_le_mul x y
  rw [Real.dist_eq] at hLip
  have htri : |f i x| ≤ |f i x-f i y|+|f i y| := by
    simpa only [sub_add_cancel] using abs_add_le (f i x-f i y) (f i y)
  have hδid : 2 * ((L : ℝ)+1) * δ = ε := by dsimp [δ]; field_simp
  have hine := mul_lt_mul_of_pos_left hdist (show 0 < (L : ℝ)+1 by positivity)
  have hy' := hi ⟨y,hy⟩
  nlinarith [mul_nonneg L.coe_nonneg (dist_nonneg (x := x) (y := y))]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.LocalGeometry
namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

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


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.LocalLipschitz.uniform_zero_on_compact.{uM} := @_root_.OAI.LipschitzCounterexample.LocalLipschitz.uniform_zero_on_compact.{uM}
