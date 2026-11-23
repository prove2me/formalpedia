-- Prove2me | solution 1 for GlobalTheory.IntegralNeighbourhoodZero.isOpen_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:05.172148+00:00
-- url     : https://prove2.me/submissions/b9780ff2-b0e1-4a1e-b7c8-32ed4fd333f2

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NsmulIntegralMemNhdsZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralNeighbourhoodZero
open IsDedekindDomain NumberField
namespace GlobalTheory.IntegralNeighbourhoodZero
theorem _root_.solution (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem fun _ => Valued.isOpen_valuationSubring _
end GlobalTheory.IntegralNeighbourhoodZero
