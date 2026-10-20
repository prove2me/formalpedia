-- Prove2me | solution 2 for OAI.LipschitzCounterexample.CompactWSC.gradMass_le_young
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:46:15.686839+00:00
-- url     : https://prove2.me/submissions/8b5172bb-cf77-48a6-9c1c-fe3393fa4878

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/EnergyEstimates.lean:L43-L72
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.gradMass_le_young. The node keeps its source
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

theorem grad_contDiff (f : Smooth H) : ContDiff ℝ ∞ (fun p => grad p f) :=
  (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp
    (f.contDiff.fderiv_right (by simp))

theorem grad_continuous (f : Smooth H) : Continuous (fun p => grad p f) :=
  f.grad_contDiff.continuous

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

theorem grad_integrable (f : Smooth H) (p q : H) :
    IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) f‖) volume 0 1 :=
  ((f.grad_continuous.comp (edge_continuous p q)).norm).intervalIntegrable _ _

theorem grad_sq_integrable (f : Smooth H) (p q : H) :
    IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) f‖^2) volume 0 1 :=
  ((f.grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable _ _

theorem gradMass_le_young (a : MolecularData H) (f : Smooth H) {t : ℝ} (ht : 0 < t) :
    gradMass a f ≤ t*a.cost+(4*t)⁻¹*gradEnergy a f := by
  have hedge (p q : H) :
      (∫ s in (0:ℝ)..1, ‖Smooth.grad (edge p q s) f‖) ≤
        t+(4*t)⁻¹*(∫ s in (0:ℝ)..1, ‖Smooth.grad (edge p q s) f‖^2) := by
    calc
      _ ≤ ∫ s in (0:ℝ)..1, t+(4*t)⁻¹*‖Smooth.grad (edge p q s) f‖^2 := by
        apply intervalIntegral.integral_mono_on (by norm_num) (grad_integrable f p q)
          (intervalIntegrable_const.add ((grad_sq_integrable f p q).const_mul _))
        intro s _
        have hsq := sq_nonneg (‖Smooth.grad (edge p q s) f‖-2*t)
        have hpos : 0 < 4*t := by positivity
        have hinv : (4*t)*((4*t)⁻¹) = 1 := mul_inv_cancel₀ hpos.ne'
        calc
          _ ≤ (t*(4*t)+‖Smooth.grad (edge p q s) f‖^2)/(4*t) :=
            (le_div_iff₀ hpos).mpr (by nlinarith)
          _ = _ := by field_simp
      _ = _ := by rw [intervalIntegral.integral_add intervalIntegrable_const
          ((grad_sq_integrable f p q).const_mul _),intervalIntegral.integral_const_mul]; simp
  calc
    gradMass a f ≤ ∑ i, (|a.coeff i| * dist (a.p i) (a.q i))*
        (t+(4*t)⁻¹*(∫ s in (0:ℝ)..1, ‖Smooth.grad (edge (a.p i) (a.q i) s) f‖^2)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hedge _ _) (mul_nonneg (abs_nonneg _) dist_nonneg)
    _ = t*a.cost+(4*t)⁻¹*gradEnergy a f := by
      simp only [MolecularData.cost,gradEnergy,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.gradMass_le_young.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.gradMass_le_young.{uH}
