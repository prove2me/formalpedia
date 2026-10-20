-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.gradEnergy_le_cost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:08:41.742284+00:00
-- url     : https://prove2.me/submissions/da427f0d-f775-4e76-b6da-73580ed35fbb

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
theorem h50c_grad_norm (f : Smooth H) (x : H) : ‖Smooth.grad x f‖ = ‖fderiv ℝ (f : H → ℝ) x‖ := by
  change ‖(InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (f : H → ℝ) x)‖ = _
  exact LinearIsometryEquiv.norm_map _ _

theorem h50c_grad_le_one (f : Smooth H) (hf : LipschitzWith 1 (f : H → ℝ)) (x : H) :
    ‖Smooth.grad x f‖ ≤ 1 := by
  rw [h50c_grad_norm]
  simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hf

theorem solution (a : MolecularData H) (f : Smooth H)
    (hf : LipschitzWith 1 (f : H → ℝ)) : gradEnergy a f ≤ a.cost := by
  unfold gradEnergy MolecularData.cost
  apply Finset.sum_le_sum
  intro i _
  have hw : 0 ≤ |a.coeff i| * dist (a.p i) (a.q i) := by positivity
  have hint : ∫ t in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖^2 ≤ 1 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (C := 1)
      (f := fun t => ‖Smooth.grad (edge (a.p i) (a.q i) t) f‖^2) (by
        intro t _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := h50c_grad_le_one f hf (edge (a.p i) (a.q i) t)
        nlinarith [norm_nonneg (Smooth.grad (edge (a.p i) (a.q i) t) f)])
    simp at this
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
  calc _ ≤ (|a.coeff i| * dist (a.p i) (a.q i)) * 1 := mul_le_mul_of_nonneg_left hint hw
    _ = _ := mul_one _

