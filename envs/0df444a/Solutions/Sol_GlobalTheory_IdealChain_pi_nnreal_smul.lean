-- Prove2me | solution 1 for GlobalTheory.IdealChain.pi_nnreal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:40:10.496828+00:00
-- url     : https://prove2.me/submissions/f2a635a5-d9be-4e58-9b83-86258702c01f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
open GlobalTheory GlobalTheory.IdealChain
namespace GlobalTheory.IdealChain
theorem _root_.solution {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : NNReal) :
    (Measure.pi fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ENNReal.coe_pow]
end GlobalTheory.IdealChain
