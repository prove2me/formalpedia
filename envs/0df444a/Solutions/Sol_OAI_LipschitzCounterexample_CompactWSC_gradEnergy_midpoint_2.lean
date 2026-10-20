-- Prove2me | solution 2 for OAI.LipschitzCounterexample.CompactWSC.gradEnergy_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:40:25.039434+00:00
-- url     : https://prove2.me/submissions/5c859651-7455-4b25-8bd8-24420c4a3214

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothCalculus.lean:L131-L146
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.gradEnergy_midpoint. The node keeps its source
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

-- ---- from OAI.Analysis.LipschitzEquivalence.HilbertBlocks ----
namespace OAI

universe uE uF uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped BigOperators

variable {E : Type uE} [AddCommGroup E] [Module ℝ E]

variable {F : Type uF} [AddCommGroup F] [Module ℝ F]

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem hilbert_midpoint_energy (x y : H) :
    ‖(1/2 : ℝ) • (x+y)‖^2 = (‖x‖^2+‖y‖^2)/2-‖x-y‖^2/4 := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [mul_pow, norm_add_sq_real, norm_sub_sq_real]
  ring

end LipschitzCounterexample.CompactWSC
end

end OAI

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

theorem gradEnergy_midpoint (a : MolecularData H) (f g : Smooth H) :
    gradEnergy a ((1/2:ℝ) • (f+g)) =
      (gradEnergy a f+gradEnergy a g)/2-gradEnergy a (f-g)/4 := by
  have he (p q : H) :
      (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) ((1/2:ℝ) • (f+g))‖^2) =
      ((∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) f‖^2)+
       (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) g‖^2))/2-
       (∫ t in (0:ℝ)..1, ‖Smooth.grad (edge p q t) (f-g)‖^2)/4 := by
    have hf : IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) f‖^2) volume 0 1 := ((f.grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable (μ := volume) (0:ℝ) 1
    have hg : IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) g‖^2) volume 0 1 := ((g.grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable (μ := volume) (0:ℝ) 1
    have hfg : IntervalIntegrable (fun t : ℝ => ‖Smooth.grad (edge p q t) (f-g)‖^2) volume 0 1 := (((f-g).grad_continuous.comp (edge_continuous p q)).norm.pow 2).intervalIntegrable (μ := volume) (0:ℝ) 1
    simp only [map_smul,map_add,hilbert_midpoint_energy,← map_sub]
    rw [intervalIntegral.integral_sub ((hf.add hg).div_const 2) (hfg.div_const 4),
      intervalIntegral.integral_div,intervalIntegral.integral_add hf hg,intervalIntegral.integral_div]
  simp only [gradEnergy,he,mul_sub,← mul_div_assoc,mul_add,Finset.sum_sub_distrib,
    ← Finset.sum_div,Finset.sum_add_distrib]

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory
open FreeSpace


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.gradEnergy_midpoint.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.gradEnergy_midpoint.{uH}
