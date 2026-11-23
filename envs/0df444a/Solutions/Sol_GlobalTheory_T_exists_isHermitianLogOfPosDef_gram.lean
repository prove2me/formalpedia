-- Prove2me | solution 1 for GlobalTheory.T.exists_isHermitianLogOfPosDef_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:51.401925+00:00
-- url     : https://prove2.me/submissions/8cf8a333-971f-4da5-9527-3dab45db6260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Theorems.Thm_GlobalTheory_ClassFin_exists_isLog_gram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι ℂ), IsUnit x.det → ∃ H : Matrix ι ι ℂ, IsLog H (xᴴ * x) := by
  first | exact @GlobalTheory.ClassFin.exists_isLog_gram | exact GlobalTheory.ClassFin.exists_isLog_gram | (intros; apply GlobalTheory.ClassFin.exists_isLog_gram <;> assumption)
end _root_.GlobalTheory.T
