-- Prove2me | solution 1 for GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:28.917057+00:00
-- url     : https://prove2.me/submissions/86f5647c-f187-4b57-8056-2f6e38785d0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviCentreDiagonalConjugationEq
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviCentreDiagonalConjugationEqStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_TorusConjProof_torusConj


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.TorusConj := by
  first | exact @GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | exact GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | (intros; apply GlobalTheory.SatakeWeyl.TorusConjProof.torusConj <;> assumption)
end _root_.GlobalTheory.T
