-- Prove2me | solution 1 for GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:04:08.158221+00:00
-- url     : https://prove2.me/submissions/5dd0120a-7a7f-4d25-9c68-a009ec7111e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContracts
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContractsStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_contract


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.Contract := by
  first | exact @GlobalTheory.SatakeWeyl.ContractProof.contract | exact GlobalTheory.SatakeWeyl.ContractProof.contract | (intros; apply GlobalTheory.SatakeWeyl.ContractProof.contract <;> assumption)
end _root_.GlobalTheory.T
