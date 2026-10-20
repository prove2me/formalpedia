-- Prove2me | solution 2 for OAI.LipschitzCounterexample.CompactWSC.product_gradient_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:02:10.0208+00:00
-- url     : https://prove2.me/submissions/a205f555-7a6c-4245-8fc3-f0a74eb53482

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothMultiplier.lean:L118-L136
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.product_gradient_error. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothMultiplier

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

theorem grad_eq (f : Smooth H) (p : H) : grad p f = gradient (f : H → ℝ) p := rfl

theorem grad_mul (f g : Smooth H) (p : H) :
    grad p (f.mul g) = f.val p • grad p g + g.val p • grad p f := by
  apply (InnerProductSpace.toDual ℝ H).injective
  simp only [grad_eq,toDual_gradient,map_add,map_smul]
  exact fderiv_mul (f.differentiable p) (g.differentiable p)

end Smooth

open FreeSpace

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothMultiplier ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe uH uIndex

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem product_gradient_error {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (φ f : Smooth H) {x : H} {D ε : ℝ}
    (hf : ‖Smooth.grad x f‖ ≤ 1) (hφ : ‖Smooth.grad x φ‖ ≤ D)
    (happrox : |φ.val x-damping s z x| ≤ ε/2)
    (hsmall : |f.val x| * D ≤ ε/2) :
    ‖Smooth.grad x (φ.mul f)-damping s z x • Smooth.grad x f‖ ≤ ε := by
  rw [Smooth.grad_mul]
  have he : φ.val x • Smooth.grad x f+f.val x • Smooth.grad x φ-
      damping s z x • Smooth.grad x f =
      (φ.val x-damping s z x) • Smooth.grad x f+f.val x • Smooth.grad x φ := by module
  rw [he]
  calc
    _ ≤ ‖(φ.val x-damping s z x) • Smooth.grad x f‖+‖f.val x • Smooth.grad x φ‖ := norm_add_le _ _
    _ = |φ.val x-damping s z x| * ‖Smooth.grad x f‖+|f.val x| * ‖Smooth.grad x φ‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ |φ.val x-damping s z x|+|f.val x| * D := by
      apply add_le_add
      · simpa using mul_le_mul_of_nonneg_left hf (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left hφ (abs_nonneg _)
    _ ≤ ε := by linarith

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter


theorem solution.{uH,uIndex} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.product_gradient_error.{uH,uIndex} := @_root_.OAI.LipschitzCounterexample.CompactWSC.product_gradient_error.{uH,uIndex}
