-- Prove2me | solution 1 for GlobalTheory.IntegralOpen.isOpen_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:12.527992+00:00
-- url     : https://prove2.me/submissions/aa5c2473-7c66-465a-8553-a0ce79e80169

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralOpen
open IsDedekindDomain NumberField
namespace GlobalTheory.IntegralOpen
theorem _root_.solution (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F),
        (a : (w : HeightOneSpectrum (RingOfIntegers F)) → HeightOneSpectrum.adicCompletion F w) v ∈
          HeightOneSpectrum.adicCompletionIntegers F v} :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun w : HeightOneSpectrum (RingOfIntegers F) => HeightOneSpectrum.adicCompletion F w)
    (A := fun w => (HeightOneSpectrum.adicCompletionIntegers F w : Set (HeightOneSpectrum.adicCompletion F w)))
    (fun _ => Valued.isOpen_valuationSubring _)
end GlobalTheory.IntegralOpen
