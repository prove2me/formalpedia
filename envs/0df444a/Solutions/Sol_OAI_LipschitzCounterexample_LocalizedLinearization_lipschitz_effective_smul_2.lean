-- Prove2me | solution 2 for OAI.LipschitzCounterexample.LocalizedLinearization.lipschitz_effective_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:41:39.912997+00:00
-- url     : https://prove2.me/submissions/e199b294-69c2-440d-abd0-fac39f6c058f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SupportedDuality.lean:L92-L120
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.LocalizedLinearization.lipschitz_effective_smul. The node keeps its source
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

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lipschitz_effective_smul (p : M → E) (φ : M → ℝ) {A B C P : ℝ≥0}
    (hp : LipschitzWith C p) (hφ : LipschitzWith B φ)
    (hA : ∀ x, |φ x| ≤ A) (hP : ∀ x, φ x ≠ 0 → ‖p x‖ ≤ P) :
    LipschitzWith (A*C+B*P) (fun x => φ x • p x) := by
  have hsmall (x y : M) (hx : ‖p x‖ ≤ P) :
      ‖φ x • p x-φ y • p y‖ ≤ (A*C+B*P : ℝ≥0) * dist x y := by
    have hid : φ x • p x-φ y • p y =
        φ y • (p x-p y)+(φ x-φ y) • p x := by
      simp only [smul_sub,sub_smul]
      abel
    rw [hid]
    calc
      _ ≤ ‖φ y • (p x-p y)‖+‖(φ x-φ y) • p x‖ := norm_add_le _ _
      _ = |φ y| * ‖p x-p y‖+|φ x-φ y| * ‖p x‖ := by simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ (A : ℝ)*(C*dist x y)+(B*dist x y)*P :=
        add_le_add (mul_le_mul (hA y) (by simpa only [dist_eq_norm] using hp.dist_le_mul x y)
          (norm_nonneg _) A.coe_nonneg)
          (mul_le_mul (hφ.dist_le_mul x y) hx (norm_nonneg _) (by positivity))
      _ = _ := by push_cast; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  by_cases hx : φ x = 0
  · by_cases hy : φ y = 0
    · simp only [hx,hy,zero_smul,sub_self,norm_zero]
      positivity
    · rw [norm_sub_rev,dist_comm]
      exact hsmall y x (hP y hy)
  · exact hsmall x y (hP x hx)

variable [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set


theorem solution.{uM,uE} : type_of% @_root_.OAI.LipschitzCounterexample.LocalizedLinearization.lipschitz_effective_smul.{uM,uE} := @_root_.OAI.LipschitzCounterexample.LocalizedLinearization.lipschitz_effective_smul.{uM,uE}
