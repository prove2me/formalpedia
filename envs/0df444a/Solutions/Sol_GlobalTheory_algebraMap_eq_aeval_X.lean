-- Prove2me | solution 1 for GlobalTheory.algebraMap_eq_aeval_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:15.772707+00:00
-- url     : https://prove2.me/submissions/af03e8cd-099a-4150-9fec-81af432332e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInversionCoordinateLocalizationPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    [Algebra k[X] B] [IsScalarTower k k[X] B] (p : k[X]) :
    algebraMap k[X] B p = aeval (algebraMap k[X] B X) p := by
  have : (IsScalarTower.toAlgHom k k[X] B) = aeval (algebraMap k[X] B X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun this p
end GlobalTheory
