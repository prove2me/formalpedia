-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.Regroup.mkU_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:21:52.165851+00:00
-- url     : https://prove2.me/submissions/dbc35088-5404-4ac0-8041-8d7939b263ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.Regroup
variable {F : Type} [Field F] [NumberField F]
variable (𝔞 𝔟 : Frac F)
namespace GlobalTheory.HeckeTwo.Regroup
theorem _root_.solution {I : FractionalIdeal (𝓞 F)⁰ F} {x y : NZ I} (ε : (𝓞 F)ˣ) (h : y.1 = ((ε : 𝓞 F) : F) * x.1) :
    Quotient.mk (unitRel I) x = Quotient.mk _ y :=
  Quotient.sound (Exists.intro ε h)
end GlobalTheory.HeckeTwo.Regroup
