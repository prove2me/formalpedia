-- Prove2me | solution 1 for GlobalTheory.T.unitary_levi_normalizes_unipotent_radical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:34.223441+00:00
-- url     : https://prove2.me/submissions/70b8f298-1dbf-456e-9285-183c7f540438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadicalStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_leviRad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.SatakeWeyl.LeviRad := by
  first | exact @GlobalTheory.SatakeWeyl.leviRad | exact GlobalTheory.SatakeWeyl.leviRad | (intros; apply GlobalTheory.SatakeWeyl.leviRad <;> assumption)
end _root_.GlobalTheory.T
