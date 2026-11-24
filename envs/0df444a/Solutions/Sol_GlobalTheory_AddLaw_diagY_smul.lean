-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagY_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:09.290809+00:00
-- url     : https://prove2.me/submissions/033bddbe-5db5-4496-a20a-4c904169d3ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_diagX_smul
import Theorems.Thm_GlobalTheory_AddLaw_diagZ_smul
import Theorems.Thm_GlobalTheory_AddLaw_negDiagY_smul


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
theorem _root_.solution (P Q : Fin 3 → R) (u v : R) :
    diagY W (u • P) (v • Q) = (u * v) ^ 2 * diagY W P Q := by
  simp only [diagY, negY_eq, diagX_smul, negDiagY_smul, diagZ_smul]
  ring1
end GlobalTheory.AddLaw
