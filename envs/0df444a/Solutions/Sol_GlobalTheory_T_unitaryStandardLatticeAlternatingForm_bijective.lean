-- Prove2me | solution 1 for GlobalTheory.T.unitaryStandardLatticeAlternatingForm_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:25.92739+00:00
-- url     : https://prove2.me/submissions/bf92afc8-b744-405d-890d-1ba13bfa2873

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeAlternatingFormBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeAlternatingFormBijectiveStatement
import Theorems.Thm_GlobalTheory_UnitaryStd_form_bijective_of_unimodular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), IsUnit S.det → Function.Bijective (GlobalTheory.UnitaryStd.form ρ g S) := by
  first | exact @GlobalTheory.UnitaryStd.form_bijective_of_unimodular | exact GlobalTheory.UnitaryStd.form_bijective_of_unimodular | (intros; apply GlobalTheory.UnitaryStd.form_bijective_of_unimodular <;> assumption)
end _root_.GlobalTheory.T
