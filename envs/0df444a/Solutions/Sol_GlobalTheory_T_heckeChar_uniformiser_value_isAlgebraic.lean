-- Prove2me | solution 1 for GlobalTheory.T.heckeChar_uniformiser_value_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:21.23673+00:00
-- url     : https://prove2.me/submissions/95089aac-849a-4a83-9e58-849f49a88c58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharUniformiserValueIsAlgebraic
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharUniformiserValueIsAlgebraicStatement
import Theorems.Thm_GlobalTheory_heckeChar_val_isAlgebraic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Host
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ), (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) → ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.heckeChar_val_isAlgebraic | exact GlobalTheory.heckeChar_val_isAlgebraic | (intros; apply GlobalTheory.heckeChar_val_isAlgebraic <;> assumption)
end _root_.GlobalTheory.T
