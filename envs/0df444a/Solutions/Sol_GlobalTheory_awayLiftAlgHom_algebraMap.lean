-- Prove2me | solution 1 for GlobalTheory.awayLiftAlgHom_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:20.137105+00:00
-- url     : https://prove2.me/submissions/f52514ac-a8ac-41d2-a896-bac08243ea89

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
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) (q : k[X]) :
    awayLiftAlgHom P f h (algebraMap k[X] (Localization.Away P) q) = f q := by
  simp [awayLiftAlgHom, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
end GlobalTheory
