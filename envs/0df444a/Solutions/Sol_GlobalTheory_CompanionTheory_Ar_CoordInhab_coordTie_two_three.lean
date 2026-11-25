-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordInhab.coordTie_two_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:34:29.767632+00:00
-- url     : https://prove2.me/submissions/6fb7db53-5a47-4487-b703-19c9331d00e9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_coordTie_spec
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_span_two_three

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory CptModel
open CoordInhab
open GlobalTheory.CompanionTheory.Ar.CoordInhab
namespace GlobalTheory.CompanionTheory.Ar.CoordInhab
theorem _root_.solution :
    CoordTie ℤ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) :=
  coordTie_spec ℤ ℚ ![2, 3] span_two_three
end GlobalTheory.CompanionTheory.Ar.CoordInhab
