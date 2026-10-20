-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.supported_pairing_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:32:42.873766+00:00
-- url     : https://prove2.me/submissions/0cfdd26b-0950-4a3f-a7f0-780c8e7b6d70

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
universe uIndex uI uE uM
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped Topology NNReal
open Filter Set
variable {M : Type uM} [MetricSpace M] [Zero M]
theorem h50b_test_sub (a b : LipZero M) (μ : Space M) :
    LocalizedLinearization.test a μ - LocalizedLinearization.test b μ =
      LocalizedLinearization.test (a - b) μ := by
  change μ.1 a - μ.1 b = μ.1 (a - b)
  rw [map_sub]

theorem h50b_abs_test_le (a : LipZero M) {K : ℝ≥0} (ha : LipschitzWith K a.1) (μ : Space M) :
    |LocalizedLinearization.test a μ| ≤ K * ‖μ‖ := by
  have h1 : |LocalizedLinearization.test a μ| ≤ ‖a‖ * ‖μ‖ := by
    change |μ.1 a| ≤ ‖a‖ * ‖μ‖
    have := μ.1.le_opNorm a
    rw [Real.norm_eq_abs] at this
    calc |μ.1 a| ≤ ‖μ.1‖ * ‖a‖ := this
      _ = ‖a‖ * ‖μ‖ := by rw [mul_comm]; rfl
  exact h1.trans (mul_le_mul_of_nonneg_right (norm_le_of_lipschitz a ha) (norm_nonneg _))

theorem h50b_test_vanish {K : Set M} (a : LipZero M) (ha : ∀ x ∈ K, a.1 x = 0) {μ : Space M}
    (hμ : μ ∈ supported K) : LocalizedLinearization.test a μ = 0 := by
  have hle : supported K ≤ LinearMap.ker (LocalizedLinearization.test a).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [LocalizedLinearization.test_point]
      exact ha x hx
    · exact (LocalizedLinearization.test a).isClosed_ker
  exact hle hμ

theorem h50b_normalized_lip (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (LocalizedLinearization.normalized f hf).1 :=
  LocalizedLinearization.lipschitz_sub_const f hf (f 0)

theorem solution {K : Set M} (hK : (0 : M) ∈ K)
    (f : M → ℝ) {C L : ℝ≥0} (hf : LipschitzWith L f) (hC : LipschitzOnWith C f K)
    (μ : Space M) (hμ : μ ∈ supported K) :
    |LocalizedLinearization.test (LocalizedLinearization.normalized f hf) μ| ≤ C * ‖μ‖ := by
  obtain ⟨g, hg, hfg⟩ := hC.extend_real
  have hvan : ∀ x ∈ K, (LocalizedLinearization.normalized f hf - LocalizedLinearization.normalized g hg).1 x = 0 := by
    intro x hx
    change (f x - f 0) - (g x - g 0) = 0
    rw [hfg hx, hfg hK]; ring
  have h1 := h50b_test_vanish _ hvan hμ
  rw [← h50b_test_sub, sub_eq_zero] at h1
  rw [h1]
  exact h50b_abs_test_le _ (h50b_normalized_lip g hg) μ

