-- Prove2me | solution 1 for GlobalTheory.MainTerm.ordGE_one_of_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:59:57.572084+00:00
-- url     : https://prove2.me/submissions/c4aceb2b-63b7-43fb-9fb4-d035ae902fc5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (OrdGE)
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
namespace GlobalTheory.MainTerm
theorem _root_.solution {C : Type} [Field C] {ι : Type} {F : MvPowerSeries ι C}
    (h : MvPowerSeries.constantCoeff F = 0) : OrdGE 1 F := by
  intro A hA
  have : A = 0 := (Finsupp.degree_eq_zero_iff A).1 (by omega)
  subst this
  simpa using h
end GlobalTheory.MainTerm
