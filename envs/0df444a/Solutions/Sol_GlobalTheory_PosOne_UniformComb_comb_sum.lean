-- Prove2me | solution 1 for GlobalTheory.PosOne.UniformComb.comb_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:32.169041+00:00
-- url     : https://prove2.me/submissions/d052cd18-980a-495e-bcb8-4d5a08ddd572

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeEqFiniteTranslateCombOfLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.PosOne GlobalTheory.PosOne.UniformComb
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage GlobalTheory.RootEx.UniformLattices
namespace GlobalTheory.PosOne.UniformComb
theorem _root_.solution {G ι : Type} (T : Finset ι) (g : ι → G) (a : ℂ) (f : G → ℂ) :
    comb (∑ t ∈ T, Finsupp.single (g t) a) f = a * ∑ t ∈ T, f (g t) := by
  unfold comb
  rw [← Finsupp.sum_finset_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _)]
end GlobalTheory.PosOne.UniformComb
