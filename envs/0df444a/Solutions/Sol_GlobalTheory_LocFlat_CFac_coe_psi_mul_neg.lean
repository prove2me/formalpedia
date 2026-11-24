-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.coe_psi_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:33:29.389302+00:00
-- url     : https://prove2.me/submissions/be093f16-53e1-41e3-ade3-5d30956878e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearOfBilinearSchwartzBruhatProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeisenbergInvariantFactorsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac
namespace GlobalTheory.LocFlat.CFac
theorem _root_.solution {k : Type} [AddGroup k] (ψ : AddChar k Circle) (a : k) : (ψ a : ℂ) * ψ (-a) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
end GlobalTheory.LocFlat.CFac
