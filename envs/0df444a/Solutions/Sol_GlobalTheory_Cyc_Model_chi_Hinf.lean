-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.chi_Hinf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:07:00.595123+00:00
-- url     : https://prove2.me/submissions/fa7f7f03-d32b-460b-aaaf-53081d3873db

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius
import Theorems.Thm_GlobalTheory_Cyc_Model_norm_sub_of_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.Model
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) {σ : GQ l} (hσ : σ ∈ Hinf K) :
    (χ σ : ℚ_[l]) = 1 := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have key : ∀ m : ℕ, ‖(χ σ : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)
    obtain ⟨a, ha, hga⟩ := hχ σ m ζ hζ.pow_eq_one
    have hmem : ζ ∈ Kinf K := (le_sup_right : _ ≤ Kinf K)
      (IntermediateField.subset_adjoin _ _ ⟨m, hζ.pow_eq_one⟩)
    have hfix : σ ζ = ζ := hσ ⟨ζ, hmem⟩
    have hb := norm_sub_of_pow_eq hζ (a := a) (b := 1) (by rw [← hga, hfix, pow_one])
    have := (Padic.nonarchimedean ((χ σ : ℚ_[l]) - (a : ℚ_[l])) _).trans (max_le ha hb)
    simpa using this
  by_contra hne
  have hpos : 0 < ‖(χ σ : ℚ_[l]) - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hpos
  exact absurd (key k) (not_le.mpr hk)
end GlobalTheory.Cyc.Model
