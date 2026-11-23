-- Prove2me | solution 1 for GlobalTheory.UnramValue.norm_algebraMap_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:43.235345+00:00
-- url     : https://prove2.me/submissions/82f9a191-d200-45ef-b077-678736f830e3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.UnramValue
theorem _root_.solution (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (Om l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l)]
  exact PadicAlgCl.norm_extends l _
end GlobalTheory.UnramValue
