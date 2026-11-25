-- Prove2me | solution 1 for GlobalTheory.BK.complDer_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:38:27.165911+00:00
-- url     : https://prove2.me/submissions/0356726e-1068-4108-b303-756eb7aa6575

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable {A' B : Type} [CommRing A'] [CommRing B] (ι : A' →+* B) (s : A')
variable {ι s}
variable {k : Type} [CommRing k] [Algebra k A'] (I : Ideal A') (D : Derivation k A' A')
namespace GlobalTheory.BK
theorem _root_.solution (r : A') :
    complDer I D (algebraMap A' _ r) = algebraMap A' _ (D r) := complDerFun_algebraMap I D r
end GlobalTheory.BK
