-- Prove2me | solution 1 for GlobalTheory.T.unitaryStandardLattice_form_complexStructure_baseChange_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:27.31861+00:00
-- url     : https://prove2.me/submissions/6d9bab45-803a-4446-928e-91df7cc92b0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeFormComplexStructureBaseCh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeFormComplexStructureBaseChStatement
import Theorems.Thm_GlobalTheory_UnitaryStd_form_cx_baseChange_pos


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
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), (S.map (Int.cast : ℤ → ℝ)).PosDef → ∀ x : ℝ ⊗[ℤ] GlobalTheory.UnitaryStd.Lat ρ g, x ≠ 0 → 0 < (GlobalTheory.UnitaryStd.form ρ g S).baseChange ℝ ((GlobalTheory.UnitaryStd.cx ρ g).baseChange ℝ x) x := by
  first | exact @GlobalTheory.UnitaryStd.form_cx_baseChange_pos | exact GlobalTheory.UnitaryStd.form_cx_baseChange_pos | (intros; apply GlobalTheory.UnitaryStd.form_cx_baseChange_pos <;> assumption)
end _root_.GlobalTheory.T
