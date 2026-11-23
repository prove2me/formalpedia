-- Prove2me | solution 1 for GlobalTheory.Cyc.IsCyc.norm_sub_one_le_of_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:27.951673+00:00
-- url     : https://prove2.me/submissions/68b3e873-54f6-4a5c-a66e-d76243da5192

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Theorems.Thm_GlobalTheory_Cyc_padic_norm_sub_le_trans
import Theorems.Thm_GlobalTheory_Cyc_norm_nat_sub_one_le_iff

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
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) (m : ℕ)
    {ζ : Om l} (hζ : IsPrimitiveRoot ζ (l ^ m)) (hg : g ζ = ζ) :
    ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  obtain ⟨a, ha, hga⟩ := h g m ζ hζ.pow_eq_one
  refine padic_norm_sub_le_trans ha ?_
  rw [norm_nat_sub_one_le_iff]
  have h0 : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have h1 : ζ ^ ((a : ℤ) - 1) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, ← hga, hg, zpow_one, div_self h0]
  have := (hζ.zpow_eq_one_iff_dvd _).1 h1
  exact_mod_cast this
end IsCyc
end GlobalTheory.Cyc
