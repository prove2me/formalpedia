-- Prove2me | solution 1 for GlobalTheory.T.charpoly_dvd_pow_finrank_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:40.8788+00:00
-- url     : https://prove2.me/submissions/888ff1b1-d06e-4a42-9622-a0963f0f33fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZeroStatement
import Theorems.Thm_GlobalTheory_CharpolyDvd_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (G : K[X]), aeval f G = 0 → f.charpoly ∣ G ^ Module.finrank K V := by
  first | exact @GlobalTheory.CharpolyDvd.main | exact GlobalTheory.CharpolyDvd.main | (intros; apply GlobalTheory.CharpolyDvd.main <;> assumption)
end _root_.GlobalTheory.T
