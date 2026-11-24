-- Prove2me | solution 1 for GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:49:32.956638+00:00
-- url     : https://prove2.me/submissions/f27d4d8d-3976-477b-ba19-277247bb1b37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Theorems.Thm_GlobalTheory_Cyc_norm_primitiveRoot_sub_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), 1 ≤ j → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ (l ^ j) → ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  first | exact @GlobalTheory.Cyc.norm_primitiveRoot_sub_one | exact GlobalTheory.Cyc.norm_primitiveRoot_sub_one | (intros; apply GlobalTheory.Cyc.norm_primitiveRoot_sub_one <;> assumption)
end _root_.GlobalTheory.T
