-- Prove2me | solution 1 for GlobalTheory.surjective_of_epi_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:43:08.302478+00:00
-- url     : https://prove2.me/submissions/7bddd6e9-aafd-41e9-9853-d5b3be053dd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Coalgebra Bialgebra HopfAlgebra WithConv
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R S : CommRingCat} (f : R ⟶ S) [CategoryTheory.Epi f]
    (hf : f.hom.Finite) : Function.Surjective f :=
  RingHom.surjective_of_epi_of_finite f hf
end GlobalTheory
