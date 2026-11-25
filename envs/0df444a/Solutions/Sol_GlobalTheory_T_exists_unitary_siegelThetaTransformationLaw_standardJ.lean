-- Prove2me | solution 1 for GlobalTheory.T.exists_unitary_siegelThetaTransformationLaw_standardJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:22:39.895626+00:00
-- url     : https://prove2.me/submissions/a70398ef-2505-48d6-8b20-00095c7a879c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandarStatement
import Theorems.Thm_GlobalTheory_SW_FourierJ_exists_trans_J


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧ TransS (Matrix.J ι ℚ) φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  first | exact @GlobalTheory.SW.FourierJ.exists_trans_J | exact GlobalTheory.SW.FourierJ.exists_trans_J | (intros; apply GlobalTheory.SW.FourierJ.exists_trans_J <;> assumption)
end _root_.GlobalTheory.T
