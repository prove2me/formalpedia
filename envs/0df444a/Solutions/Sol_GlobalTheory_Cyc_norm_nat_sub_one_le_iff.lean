-- Prove2me | solution 1 for GlobalTheory.Cyc.norm_nat_sub_one_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:57.894543+00:00
-- url     : https://prove2.me/submissions/280a900e-2e01-4c98-a44e-24ace3aa5a1e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (a m : ℕ) :
    ‖(a : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ↔ ((l : ℤ) ^ m) ∣ (a : ℤ) - 1 := by
  rw [← Padic.norm_int_le_pow_iff_dvd]
  push_cast
  rfl
end GlobalTheory.Cyc
