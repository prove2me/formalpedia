-- Prove2me | solution 1 for GlobalTheory.T.tsum_schwartzBruhatLevel_eq_sum_residueCosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:44.681789+00:00
-- url     : https://prove2.me/submissions/91d7e29c-6882-4e94-aaff-179943fac7d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Theorems.Thm_GlobalTheory_SW_FourierJ_tsum_level_eq_sum_cosets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → HasLevel R φ → Summable (fun x => φ x * F x) → ∑' x, φ x * F x = ∑ n : κ → ι → Fin (R * R), φ (rep R n) * ∑' m : κ → ι → ℤ, F (rep R n + (R : ℚ) • zm m) := by
  first | exact @GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets | exact GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets | (intros; apply GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets <;> assumption)
end _root_.GlobalTheory.T
