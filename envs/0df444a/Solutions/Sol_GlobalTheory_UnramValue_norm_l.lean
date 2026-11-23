-- Prove2me | solution 1 for GlobalTheory.UnramValue.norm_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:39.993623+00:00
-- url     : https://prove2.me/submissions/025c1fb0-a9f1-4fb9-923a-c854d082ccc2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Theorems.Thm_GlobalTheory_UnramValue_norm_algebraMap_int

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
theorem _root_.solution : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h := norm_algebraMap_int (l := l) (l : ℤ_[l])
  rwa [map_natCast, PadicInt.norm_p] at h
end GlobalTheory.UnramValue
