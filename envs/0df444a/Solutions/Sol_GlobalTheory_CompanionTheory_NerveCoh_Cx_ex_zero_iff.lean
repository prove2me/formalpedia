-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.Cx.ex_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:25:57.519189+00:00
-- url     : https://prove2.me/submissions/7fde4c12-9327-4663-b8d0-101d7d3b609f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.NerveCoh
namespace Cx
theorem _root_.solution {A : Cx R} : A.Ex 0 ↔ ∀ x, A.d 0 x = 0 → x = 0 :=
  injective_iff_map_eq_zero (A.d 0)
end Cx
end GlobalTheory.CompanionTheory.NerveCoh
