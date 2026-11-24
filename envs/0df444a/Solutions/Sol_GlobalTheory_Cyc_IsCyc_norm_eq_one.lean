-- Prove2me | solution 1 for GlobalTheory.Cyc.IsCyc.norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:59.275736+00:00
-- url     : https://prove2.me/submissions/27a099a2-7745-4717-91c4-e7e67256c947

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_norm_le_one

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
    ‖(χ g : ℚ_[l])‖ = 1 := by
  have h1 := h.norm_le_one g
  have h2 := h.norm_le_one g⁻¹
  have h3 : ‖(χ g : ℚ_[l])‖ * ‖(χ g⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]; simp
  have h4 := norm_nonneg (χ g : ℚ_[l])
  nlinarith
end IsCyc
end GlobalTheory.Cyc
