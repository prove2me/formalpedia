-- Prove2me | solution 1 for GlobalTheory.CharpolyDvd.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:50.093691+00:00
-- url     : https://prove2.me/submissions/1099d3fa-1eab-4e1c-aec6-eb9c479e395a

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Theorems.Thm_GlobalTheory_CharpolyDvd_charpoly_dvd_pow_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
open GlobalTheory GlobalTheory.CharpolyDvd
namespace GlobalTheory.CharpolyDvd
theorem _root_.solution : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (G : K[X]), aeval f G = 0 → f.charpoly ∣ G ^ Module.finrank K V :=
  fun f G hG => charpoly_dvd_pow_finrank f G hG
end GlobalTheory.CharpolyDvd
