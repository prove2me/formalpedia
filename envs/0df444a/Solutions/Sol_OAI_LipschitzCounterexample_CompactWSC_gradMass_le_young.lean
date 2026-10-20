-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.gradMass_le_young
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:10:25.311344+00:00
-- url     : https://prove2.me/submissions/a04b2d9c-9db5-4f1e-8164-78207adf6a2f

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

theorem h50c_grad_cont (f : Smooth H) (p q : H) :
    Continuous (fun t : ℝ => Smooth.grad (edge p q t) f) := by
  change Continuous (fun t : ℝ => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (f : H → ℝ) (edge p q t)))
  have he : Continuous (fun t : ℝ => edge p q t) := by
    unfold edge; exact continuous_const.add (continuous_id.smul continuous_const)
  exact (InnerProductSpace.toDual ℝ H).symm.continuous.comp
    ((f.contDiff.continuous_fderiv (by simp)).comp he)

theorem solution (a : MolecularData H) (f : Smooth H) {t : ℝ} (ht : 0 < t) :
    gradMass a f ≤ t*a.cost+(4*t)⁻¹*gradEnergy a f := by
  unfold gradMass gradEnergy MolecularData.cost
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  set w := |a.coeff i| * dist (a.p i) (a.q i) with hw
  have hw0 : 0 ≤ w := by positivity
  set g : ℝ → H := fun s => Smooth.grad (edge (a.p i) (a.q i) s) f with hg
  have hc : Continuous g := h50c_grad_cont f _ _
  have hc1 : Continuous (fun s => ‖g s‖) := hc.norm
  have hc2 : Continuous (fun s => ‖g s‖ ^ 2) := hc.norm.pow 2
  have hpt : ∀ s, ‖g s‖ ≤ t + (4 * t)⁻¹ * ‖g s‖ ^ 2 := by
    intro s
    have h1 : 0 ≤ (‖g s‖ - 2 * t) ^ 2 := sq_nonneg _
    rw [← sub_nonneg]
    have : t + (4 * t)⁻¹ * ‖g s‖ ^ 2 - ‖g s‖ = (4 * t)⁻¹ * (‖g s‖ - 2 * t) ^ 2 := by
      field_simp; ring
    rw [this]; positivity
  have hc3 : Continuous (fun s => t + (4 * t)⁻¹ * ‖g s‖ ^ 2) := continuous_const.add (continuous_const.mul hc2)
  have hmono : ∫ s in (0:ℝ)..1, ‖g s‖ ≤ ∫ s in (0:ℝ)..1, (t + (4 * t)⁻¹ * ‖g s‖ ^ 2) :=
    intervalIntegral.integral_mono_on zero_le_one (hc1.intervalIntegrable 0 1) (hc3.intervalIntegrable 0 1)
      (fun s _ => hpt s)
  have hc4 : Continuous (fun s => (4 * t)⁻¹ * ‖g s‖ ^ 2) := continuous_const.mul hc2
  have e : ∫ s in (0:ℝ)..1, (t + (4 * t)⁻¹ * ‖g s‖ ^ 2) = t + (4 * t)⁻¹ * ∫ s in (0:ℝ)..1, ‖g s‖ ^ 2 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (hc4.intervalIntegrable 0 1), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul]
    simp
  have hint : ∫ s in (0:ℝ)..1, ‖g s‖ ≤ t + (4 * t)⁻¹ * ∫ s in (0:ℝ)..1, ‖g s‖ ^ 2 := e ▸ hmono
  calc w * ∫ s in (0:ℝ)..1, ‖g s‖ ≤ w * (t + (4 * t)⁻¹ * ∫ s in (0:ℝ)..1, ‖g s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hint hw0
    _ = _ := by ring

