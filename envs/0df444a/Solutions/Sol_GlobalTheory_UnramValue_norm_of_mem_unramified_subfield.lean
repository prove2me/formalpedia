-- Prove2me | solution 1 for GlobalTheory.UnramValue.norm_of_mem_unramified_subfield
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:03.566278+00:00
-- url     : https://prove2.me/submissions/3f246dd6-5d55-4adc-b1bb-772de9c40c80

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Theorems.Thm_GlobalTheory_UnramValue_norm_of_mem_Kur

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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : Om l),
    x ∈ K0 K → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by
  intro l _ K x hx h0
  unfold K0 at hx
  exact norm_of_mem_Kur hx.2 h0
end GlobalTheory.UnramValue
