-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:36:10.69434+00:00
-- url     : https://prove2.me/submissions/f957e69e-a663-4649-b5a5-bbfff90b993d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Theorems.Thm_GlobalTheory_SW_FourierJ_haar_eq_sum_rep


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
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ : Matrix κ ι ℚ → ℂ), 0 < R → HasLevel R φ → haar φ = ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ * ∑ n : κ → ι → Fin (R * R), φ (rep R n) := by
  first | exact @GlobalTheory.SW.FourierJ.haar_eq_sum_rep | exact GlobalTheory.SW.FourierJ.haar_eq_sum_rep | (intros; apply GlobalTheory.SW.FourierJ.haar_eq_sum_rep <;> assumption)
end _root_.GlobalTheory.T
