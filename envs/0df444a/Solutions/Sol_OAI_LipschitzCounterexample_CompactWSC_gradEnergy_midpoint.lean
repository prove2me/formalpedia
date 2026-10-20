-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.gradEnergy_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:12:43.128547+00:00
-- url     : https://prove2.me/submissions/1d20d942-ad25-4553-a207-b91e13fbffcc

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
open FreeSpace
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

theorem solution (a : MolecularData H) (f g : Smooth H) :
    gradEnergy a ((1/2:ℝ) • (f+g)) =
      (gradEnergy a f+gradEnergy a g)/2-gradEnergy a (f-g)/4 := by
  unfold gradEnergy
  rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hpt : ∀ s, ‖Smooth.grad (edge (a.p i) (a.q i) s) ((1/2:ℝ) • (f+g))‖^2 =
      (‖Smooth.grad (edge (a.p i) (a.q i) s) f‖^2 + ‖Smooth.grad (edge (a.p i) (a.q i) s) g‖^2)/2 - ‖Smooth.grad (edge (a.p i) (a.q i) s) (f-g)‖^2/4 := by
    intro s
    rw [map_smul, map_add, map_sub, norm_smul, mul_pow, norm_add_sq_real, norm_sub_sq_real]
    norm_num
    ring
  simp_rw [hpt]
  have c1 : Continuous (fun s => ‖Smooth.grad (edge (a.p i) (a.q i) s) f‖^2) := (h50c_grad_cont f _ _).norm.pow 2
  have c2 : Continuous (fun s => ‖Smooth.grad (edge (a.p i) (a.q i) s) g‖^2) := (h50c_grad_cont g _ _).norm.pow 2
  have c3 : Continuous (fun s => ‖Smooth.grad (edge (a.p i) (a.q i) s) (f-g)‖^2) := (h50c_grad_cont (f-g) _ _).norm.pow 2
  have c12 : Continuous (fun s => (‖Smooth.grad (edge (a.p i) (a.q i) s) f‖^2 + ‖Smooth.grad (edge (a.p i) (a.q i) s) g‖^2)/2) := (c1.add c2).div_const 2
  have c3' : Continuous (fun s => ‖Smooth.grad (edge (a.p i) (a.q i) s) (f-g)‖^2/4) := c3.div_const 4
  rw [intervalIntegral.integral_sub (c12.intervalIntegrable 0 1) (c3'.intervalIntegrable 0 1),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_add (c1.intervalIntegrable 0 1) (c2.intervalIntegrable 0 1)]
  ring

