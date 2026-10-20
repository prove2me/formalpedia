-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.prefix_radius_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:43:20.218345+00:00
-- url     : https://prove2.me/submissions/bdfe5f4b-4ffa-437d-b953-1b3750d201ec

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/Multipliers.lean:L122-L135
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.prefix_radius_approx. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzEquivalence.SeparableCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uI uE uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]
end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace Topology
variable {E : ℕ → Type uE} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]

end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set CoordinateSpaces

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.FreeSpace
open scoped Topology NNReal
open Filter Set
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem point_mem_supported {K : Set M} {x : M} (hx : x ∈ K) : point x ∈ supported K :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x,hx,rfl⟩)

end LipschitzCounterexample.FreeSpace

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.CoordinateSpaces

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SupportedDuality ----
namespace OAI

universe uM uE

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

theorem exists_finite_approx (μ : Space M) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : M →₀ ℝ, ‖μ - Finsupp.linearCombination ℝ point a‖ < ε := by
  obtain ⟨a,ha⟩ := dense_combinations.exists_dist_lt μ hε
  exact ⟨a,by simpa only [dist_eq_norm] using ha⟩

theorem combination_mem_supported (a : M →₀ ℝ) {K : Set M}
    (ha : ∀ x ∈ a.support, x ∈ K) : Finsupp.linearCombination ℝ point a ∈ supported K := by
  rw [Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ (fun x hx => Submodule.smul_mem _ _ (point_mem_supported (ha x hx)))

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.Multipliers ----
namespace OAI

universe uM uE

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

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem supported_mono {K S : Set M} (h : K ⊆ S) : supported K ≤ supported S :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono h))

theorem Approximable.mono {μ : Space M} {K S : Set M} {ε : ℝ}
    (h : Approximable μ K ε) (hKS : K ⊆ S) : Approximable μ S ε := by
  obtain ⟨ν,hν,hn⟩ := h
  exact ⟨ν,supported_mono hKS hν,hn⟩

theorem finite_bounded {A : Finset M} : ∃ R : ℝ, 0 < R ∧ ∀ x ∈ A, dist x 0 ≤ R := by
  classical
  refine ⟨1+∑ x ∈ A, dist x 0,by positivity,?_⟩
  intro x hx
  have h := Finset.single_le_sum (fun y (_hy : y ∈ A) => dist_nonneg (x := y) (y := 0)) hx
  linarith

theorem exists_radius_approx (μ : Space M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ Approximable μ (Metric.closedBall 0 R) ε := by
  obtain ⟨a,ha⟩ := exists_finite_approx μ hε
  obtain ⟨R,hR,hA⟩ := finite_bounded (A := a.support)
  refine ⟨R,hR,Finsupp.linearCombination ℝ point a,?_,ha⟩
  exact combination_mem_supported a (fun x hx => hA x hx)

theorem prefix_radius_approx (μ : ℕ → Space M) {ε : ℝ} (hε : 0 < ε)
    (N : ℕ) (r : ℝ) : ∃ R : ℝ, r ≤ R ∧ 0 < R ∧
      ∀ i < N, Approximable (μ i) (Metric.closedBall 0 R) ε := by
  induction N with
  | zero => exact ⟨max (r+1) 1,by exact (le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _),
      lt_of_lt_of_le zero_lt_one (le_max_right _ _),by simp⟩
  | succ N ih =>
    obtain ⟨R,hr,hR,hN⟩ := ih
    obtain ⟨S,hS,hμ⟩ := exists_radius_approx (μ N) hε
    refine ⟨max R S,hr.trans (le_max_left _ _),hR.trans_le (le_max_left _ _),?_⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · exact (hN i hi).mono (Metric.closedBall_subset_closedBall (le_max_left _ _))
    · exact hμ.mono (Metric.closedBall_subset_closedBall (le_max_right _ _))

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


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.prefix_radius_approx.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.prefix_radius_approx.{uM}
