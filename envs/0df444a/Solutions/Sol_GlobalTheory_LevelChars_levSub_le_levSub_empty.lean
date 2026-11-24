-- Prove2me | solution 1 for GlobalTheory.LevelChars.levSub_le_levSub_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:44:45.576903+00:00
-- url     : https://prove2.me/submissions/71bb68c8-7cff-4eec-ae81-7864da021c21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteChars
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassGroupIdelicFiniteIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LevelChars
namespace GlobalTheory.LevelChars
theorem _root_.solution (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) :
    levSub L S N ≤ levSub L ∅ 0 := fun a ha v => ⟨(ha v).1, fun h => absurd h (Set.notMem_empty v)⟩
end GlobalTheory.LevelChars
