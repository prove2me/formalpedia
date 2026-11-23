-- Prove2me | solution 1 for GlobalTheory.Cyc.IsCyc.norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:38.399316+00:00
-- url     : https://prove2.me/submissions/5bef40da-40f5-4404-ab05-2c9c664d6f48

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Theorems.Thm_GlobalTheory_Cyc_padic_norm_sub_le_trans

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
namespace IsCyc
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := h g 0 1 (one_pow _)
  have h2 : ‖(a : ℚ_[l]) - 0‖ ≤ 1 := by
    rw [sub_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _
  simp only [Nat.cast_zero, neg_zero, zpow_zero] at ha
  simpa using padic_norm_sub_le_trans ha h2
end IsCyc
end GlobalTheory.Cyc
