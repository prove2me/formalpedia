-- Prove2me | solution 1 for GlobalTheory.NormalDescent.reverse_map_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:12.915545+00:00
-- url     : https://prove2.me/submissions/7b00683c-4632-4fe9-b238-d4312ca58e86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyMulBaseChangeFiniteMapOfIsPushoutStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCharpolyBaseChangeIntegrallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffMapOfIsPushout

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
open GlobalTheory GlobalTheory.NormalDescent
namespace GlobalTheory.NormalDescent
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]
end GlobalTheory.NormalDescent
