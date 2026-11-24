-- Prove2me | solution 1 for GlobalTheory.SplitWeil.map_curry_symm_pi_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:56:05.86973+00:00
-- url     : https://prove2.me/submissions/2c15f33a-3e56-4892-8e0f-2e14cc373272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker
open GlobalTheory GlobalTheory.SplitWeil
namespace GlobalTheory.SplitWeil
theorem _root_.solution {X a b : Type} [MeasurableSpace X] [Fintype a] [Fintype b] (ν : Measure X)
    [SigmaFinite ν] :
    Measure.map (MeasurableEquiv.curry b a X).symm (Measure.pi fun _ : b => Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : b × a => ν := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.curry b a X).symm.measurable (MeasurableSet.univ_pi hs)]
  have hpre : (MeasurableEquiv.curry b a X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : b => Set.univ.pi fun j : a => s (i, j) := by
    ext x
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]
end GlobalTheory.SplitWeil
