-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.pairing_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:45:01.50542+00:00
-- url     : https://prove2.me/submissions/47aa8b05-b58f-41c0-8050-9fb68089f978

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/Multipliers.lean:L148-L163
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.pairing_difference_le. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzEquivalence.Localization ----
namespace OAI

universe uM uV

noncomputable section
namespace LipschitzCounterexample

namespace LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem norm_test_apply_le (f : FreeSpace.LipZero M) (μ : FreeSpace.Space M) :
    ‖test f μ‖ ≤ ‖f‖ * ‖μ‖ := by
  change ‖μ.1 f‖ ≤ ‖f‖ * ‖μ.1‖
  simpa only [mul_comm] using μ.1.le_opNorm f

theorem norm_normalized_le (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) :
    ‖normalized f hf‖ ≤ C := FreeSpace.norm_le_of_lipschitz _ (by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [normalized, Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y)

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

theorem supported_le_ker {K : Set M} (T : Space M →L[ℝ] ℝ)
    (hT : ∀ x ∈ K, T (point x) = 0) : supported K ≤ T.ker := by
  apply Submodule.topologicalClosure_minimal _ _ T.isClosed_ker
  apply Submodule.span_le.mpr
  rintro _ ⟨x,hx,rfl⟩
  exact hT x hx

end LipschitzCounterexample.FreeSpace

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.CoordinateSpaces

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

theorem test_eq_of_agree {K : Set M} (h0 : (0 : M) ∈ K)
    (f g : M → ℝ) {C D : ℝ≥0} (hf : LipschitzWith C f) (hg : LipschitzWith D g)
    (he : ∀ x ∈ K, f x = g x) {ν : Space M} (hν : ν ∈ supported K) :
    test (normalized f hf) ν = test (normalized g hg) ν := by
  have hker : supported K ≤ (test (normalized f hf)-test (normalized g hg)).ker := by
    apply supported_le_ker
    intro x hx
    change (f x-f 0)-(g x-g 0) = 0
    rw [he x hx,he 0 h0,sub_self]
  exact sub_eq_zero.mp (hker hν)

theorem pairing_difference_le {K : Set M} (h0 : (0 : M) ∈ K)
    (f g : M → ℝ) {C D : ℝ≥0} (hf : LipschitzWith C f) (hg : LipschitzWith D g)
    (he : ∀ x ∈ K, f x = g x) (μ ν : Space M) (hν : ν ∈ supported K) :
    |test (normalized f hf) μ-test (normalized g hg) μ| ≤ (C+D)*‖μ-ν‖ := by
  have heq := test_eq_of_agree h0 f g hf hg he hν
  have hid : test (normalized f hf) μ-test (normalized g hg) μ =
      test (normalized f hf) (μ-ν)-test (normalized g hg) (μ-ν) := by
    rw [map_sub,map_sub,heq]
    ring
  rw [hid]
  apply (abs_sub _ _).trans
  have hf' := (norm_test_apply_le (normalized f hf) (μ-ν)).trans
    (mul_le_mul_of_nonneg_right (norm_normalized_le f hf) (norm_nonneg _))
  have hg' := (norm_test_apply_le (normalized g hg) (μ-ν)).trans
    (mul_le_mul_of_nonneg_right (norm_normalized_le g hg) (norm_nonneg _))
  simpa only [Real.norm_eq_abs,NNReal.coe_add,add_mul] using add_le_add hf' hg'

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


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.pairing_difference_le.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.pairing_difference_le.{uM}
