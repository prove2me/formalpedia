-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagXYZ_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:24.39479+00:00
-- url     : https://prove2.me/submissions/a234d1f0-11dd-471d-b856-c337e1823f73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_diagX_self
import Theorems.Thm_GlobalTheory_AddLaw_diagZ_self
import Theorems.Thm_GlobalTheory_AddLaw_negDiagY_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {R S : Type*} [CommRing R] [CommRing S]
variable {W : Projective R}
namespace GlobalTheory.AddLaw
theorem _root_.solution {P : Fin 3 → R} (hP : W.Equation P) : diagXYZ W P P = W.dblXYZ P := by
  rw [diagXYZ, diagY, diagX_self hP, negDiagY_self hP, diagZ_self hP, dblXYZ, dblY]
end GlobalTheory.AddLaw
