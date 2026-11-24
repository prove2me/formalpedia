-- Prove2me | solution 1 for GlobalTheory.Cyc.IsCyc.fix_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:58.398465+00:00
-- url     : https://prove2.me/submissions/6b5e5b8f-de68-4e84-b6da-586244322ec1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Theorems.Thm_GlobalTheory_Cyc_exists_primRoot_pow
import Theorems.Thm_GlobalTheory_Cyc_padic_norm_sub_le_trans
import Theorems.Thm_GlobalTheory_Cyc_norm_nat_sub_one_le_iff
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_norm_sub_one_le_of_prim

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
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) (m : ℕ) :
    (∀ ζ : Om l, ζ ^ (l ^ m) = 1 → g ζ = ζ) ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  constructor
  · intro hg
    obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) m
    exact h.norm_sub_one_le_of_prim g m hζ (hg ζ hζ.pow_eq_one)
  · intro hg ζ hζ
    obtain ⟨a, ha, hga⟩ := h g m ζ hζ
    rw [norm_sub_rev] at ha
    obtain ⟨c, hc⟩ := (norm_nat_sub_one_le_iff a m).1 (padic_norm_sub_le_trans ha hg)
    have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hζ
      exact zero_ne_one hζ
    have ha' : (a : ℤ) = ((l ^ m : ℕ) : ℤ) * c + 1 := by push_cast; linarith
    rw [hga, ← zpow_natCast, ha', zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, one_mul,
      zpow_one]
end IsCyc
end GlobalTheory.Cyc
