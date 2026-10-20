-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.product_gradient_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:14:30.332975+00:00
-- url     : https://prove2.me/submissions/3689efeb-3ab0-48d3-9ae0-964af24307bb

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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothMultiplier

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH uIndex
open scoped ContDiff BigOperators NNReal Topology
open Set Filter
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

theorem h50c_grad_mul (φ f : Smooth H) (x : H) :
    Smooth.grad x (φ.mul f) = φ.val x • Smooth.grad x f + f.val x • Smooth.grad x φ := by
  change (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (fun y => φ.val y * f.val y) x) =
    φ.val x • (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (f : H → ℝ) x) +
      f.val x • (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (φ : H → ℝ) x)
  rw [fderiv_fun_mul (φ.differentiable x) (f.differentiable x), map_add, map_smul, map_smul]

theorem solution {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (φ f : Smooth H) {x : H} {D ε : ℝ}
    (hf : ‖Smooth.grad x f‖ ≤ 1) (hφ : ‖Smooth.grad x φ‖ ≤ D)
    (happrox : |φ.val x-damping s z x| ≤ ε/2)
    (hsmall : |f.val x| * D ≤ ε/2) :
    ‖Smooth.grad x (φ.mul f)-damping s z x • Smooth.grad x f‖ ≤ ε := by
  rw [h50c_grad_mul]
  have e : φ.val x • Smooth.grad x f + f.val x • Smooth.grad x φ - damping s z x • Smooth.grad x f =
      (φ.val x - damping s z x) • Smooth.grad x f + f.val x • Smooth.grad x φ := by
    rw [sub_smul]; abel
  rw [e]
  calc _ ≤ ‖(φ.val x - damping s z x) • Smooth.grad x f‖ + ‖f.val x • Smooth.grad x φ‖ := norm_add_le _ _
    _ = |φ.val x - damping s z x| * ‖Smooth.grad x f‖ + |f.val x| * ‖Smooth.grad x φ‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (ε/2) * 1 + |f.val x| * D := by
        gcongr
        exact le_trans (abs_nonneg _) happrox
    _ ≤ ε := by linarith

