-- Prove2me | solution 1 for GlobalTheory.T.one_le_detW_of_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:16:58.778808+00:00
-- url     : https://prove2.me/submissions/c1a68abe-8bb8-4c50-adac-a7f257eff5c6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OneLeDetW
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OneLeDetWStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_one_le_detW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW <;> assumption)
end _root_.GlobalTheory.T
