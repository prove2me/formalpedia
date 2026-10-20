-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.radius_escape_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:47:32.119326+00:00
-- url     : https://prove2.me/submissions/7a6b1a31-b7af-4aed-8dd1-88cc369cce94

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/RadiusReduction.lean:L20-L69
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.radius_escape_step. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_exists_vanishing_test
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_pairing_difference_le
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_prefix_radius_approx

-- ---- from OAI.Analysis.LipschitzEquivalence.Localization ----
namespace OAI

universe uM uV

noncomputable section
namespace LipschitzCounterexample

namespace LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

omit [Zero M] in
theorem cutoff_one (z : M) {s : ℝ≥0} (hs : 0 < s) {x : M} (hx : dist x z ≤ s / 2) :
    cutoff z s x = 1 := by
  have hs' : 0 < (s : ℝ) := hs
  have hmul : (2 / (s : ℝ)) * dist x z ≤ 1 := by
    calc
      _ ≤ (2 / (s : ℝ)) * ((s : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ = 1 := by field_simp
  unfold cutoff
  rw [min_eq_left (by linarith)]
  norm_num

end LocalizedLinearization

end LipschitzCounterexample
end

end OAI

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

theorem finite_bounded {A : Finset M} : ∃ R : ℝ, 0 < R ∧ ∀ x ∈ A, dist x 0 ≤ R := by
  classical
  refine ⟨1+∑ x ∈ A, dist x 0,by positivity,?_⟩
  intro x hx
  have h := Finset.single_le_sum (fun y (_hy : y ∈ A) => dist_nonneg (x := y) (y := 0)) hx
  linarith

end LipschitzCounterexample.FreeSpace

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

theorem radius_escape_step {μ : ℕ → Space M} {ε : ℝ} (hε : 0 < ε)
    (hfail : ∀ R : ℝ, 0 < R → ∃ i, ¬ Approximable (μ i) (Metric.closedBall 0 R) ε)
    (p : ℕ) (r : ℝ) : ∃ i : ℕ, ∃ s : ℝ, ∃ g : M → ℝ,
      p < i ∧ r < s ∧ LipschitzWith 3 g ∧ g 0 = 0 ∧
      (∀ x, dist x 0 ≤ r → g x = 0) ∧ (∀ x, s ≤ dist x 0 → g x = 0) ∧
      ∀ hg : LipschitzWith 3 g, ε/2 < |test (normalized g hg) (μ i)| := by
  classical
  obtain ⟨R,hr,hR,hprefix⟩ := prefix_radius_approx μ hε (p+1) r
  obtain ⟨i,hi⟩ := hfail R hR
  have hip : p < i := by
    by_contra h
    exact hi (hprefix i (Nat.lt_succ_of_le (le_of_not_gt h)))
  have hfar : ∀ ν : Space M, ν ∈ supported (Metric.closedBall 0 R) → ε ≤ ‖μ i-ν‖ := by
    intro ν hν
    exact le_of_not_gt (fun h => hi ⟨ν,hν,h⟩)
  obtain ⟨f,hf,hf0,hfR,hlarge⟩ := exists_vanishing_test (Metric.closedBall 0 R) (μ i) hfar
  obtain ⟨a,ha⟩ := exists_finite_approx (μ i) (show 0 < ε/16 by positivity)
  obtain ⟨T,hT,hA⟩ := finite_bounded (A := a.support)
  let s : ℝ≥0 := ⟨2*(T+|r|+1),by positivity⟩
  have hs : 0 < s := by change 0 < 2*(T+|r|+1); positivity
  let g : M → ℝ := fun x => f x * cutoff 0 s x
  have hg : LipschitzWith 3 g := by
    simpa only [mul_one] using cutoff_product_lipschitz 0 hs f hf hf0
  refine ⟨i,s,g,hip,?_,hg,by simp [g,hf0],?_,?_,?_⟩
  · change r < 2*(T+|r|+1)
    linarith [le_abs_self r,abs_nonneg r]
  · intro x hx
    have hz := hfR x (show x ∈ Metric.closedBall 0 R from hx.trans hr)
    simp [g,hz]
  · intro x hx
    simp [g,cutoff_zero 0 hs hx]
  · intro hg'
    let K : Set M := insert 0 (a.support : Set M)
    have he (x : M) (hx : x ∈ K) : f x = g x := by
      rcases hx with rfl | hx
      · simp [g,hf0]
      · have hdist : dist x 0 ≤ (s : ℝ)/2 := by
          have hAx := hA x hx
          change dist x 0 ≤ 2*(T+|r|+1)/2
          linarith [abs_nonneg r]
        simp [g,cutoff_one 0 hs hdist]
    have haK : Finsupp.linearCombination ℝ point a ∈ supported K :=
      combination_mem_supported a (fun x hx => Set.mem_insert_of_mem 0 hx)
    have hdiff := pairing_difference_le (show (0 : M) ∈ K from Set.mem_insert _ _) f g hf hg'
      he (μ i) (Finsupp.linearCombination ℝ point a) haK
    have hl := hlarge hf
    norm_num at hdiff
    have habs := le_abs_self (test (normalized f hf) (μ i)-test (normalized g hg') (μ i))
    have habsg := le_abs_self (test (normalized g hg') (μ i))
    linarith

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


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.radius_escape_step.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.radius_escape_step.{uM}
