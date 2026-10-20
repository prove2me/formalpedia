-- Prove2me | solution 2 for OAI.LipschitzCounterexample.CompactWSC.gradEnergy_le_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:44:23.063722+00:00
-- url     : https://prove2.me/submissions/0ede8bc7-0e16-4361-8ef5-48b6fd1e1954

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/EnergyEstimates.lean:L21-L33
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.gradEnergy_le_cost. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothCalculus ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

namespace Smooth

theorem norm_grad (f : Smooth H) (p : H) : ‖grad p f‖ = ‖fderiv ℝ (f : H → ℝ) p‖ :=
  (InnerProductSpace.toDual ℝ H).symm.norm_map _

theorem grad_contDiff (f : Smooth H) : ContDiff ℝ ∞ (fun p => grad p f) :=
  (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp
    (f.contDiff.fderiv_right (by simp))

theorem grad_continuous (f : Smooth H) : Continuous (fun p => grad p f) :=
  f.grad_contDiff.continuous

theorem grad_norm_le {C : ℝ≥0} (f : Smooth H) (h : LipschitzWith C (f : H → ℝ)) (p : H) :
    ‖grad p f‖ ≤ C := by
  rw [norm_grad]
  exact norm_fderiv_le_of_lipschitz ℝ h

end Smooth

theorem edge_continuous {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (p q : H) : Continuous (edge p q) := by
  unfold edge
  fun_prop

open FreeSpace

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.EnergyEstimates ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem grad_sq_integrable (f : Smooth H) (p q : H) :
    IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) f‖^2) volume 0 1 :=
  ((f.grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable _ _

theorem gradEnergy_le_cost (a : MolecularData H) (f : Smooth H)
    (hf : LipschitzWith 1 (f : H → ℝ)) : gradEnergy a f ≤ a.cost := by
  apply Finset.sum_le_sum
  intro i _
  have hi : (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖^2) ≤ 1 := by
    calc
      _ ≤ ∫ _t in (0:ℝ)..1, (1:ℝ) := intervalIntegral.integral_mono_on (by norm_num)
        (grad_sq_integrable f _ _) (intervalIntegrable_const) (fun t _ => by
          have := f.grad_norm_le hf (edge (a.p i) (a.q i) t)
          norm_num only [NNReal.coe_one] at this
          nlinarith [norm_nonneg (Smooth.grad (edge (a.p i) (a.q i) t) f)])
      _ = 1 := by simp
  simpa using mul_le_mul_of_nonneg_left hi (mul_nonneg (abs_nonneg (a.coeff i)) dist_nonneg)

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.gradEnergy_le_cost.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.gradEnergy_le_cost.{uH}
