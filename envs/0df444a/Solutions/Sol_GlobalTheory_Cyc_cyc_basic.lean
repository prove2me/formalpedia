-- Prove2me | solution 1 for GlobalTheory.Cyc.cyc_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:24:54.688886+00:00
-- url     : https://prove2.me/submissions/1136e76d-72ea-48d3-bc53-b178d62f9f89

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_fix_iff
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_norm_eq_one
import Theorems.Thm_GlobalTheory_Cyc_exists_zpow_neg_lt
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_continuous
import Theorems.Thm_GlobalTheory_Cyc_mem_fixingSubgroup_adjoin_iff

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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ → (∀ g, ‖(χ g : ℚ_[l])‖ = 1) ∧ Continuous (fun g => (χ g : ℚ_[l])) ∧ ∀ (K : FinExt l) (g : GQ l), g ∈ (K0 K).fixingSubgroup → ((∀ j : ℕ, g ∈ Gj K j ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) ∧ (g ∈ Hinf K ↔ χ g = 1)) := by
  intro l _ χ h
  refine ⟨h.norm_eq_one, h.continuous, fun K g hg => ⟨fun j => ?_, ?_⟩⟩
  · rw [Gj, Ks, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
      mem_fixingSubgroup_adjoin_iff, ← h.fix_iff]
    exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  · rw [Hinf, Kinf, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
      mem_fixingSubgroup_adjoin_iff]
    constructor
    · rintro ⟨-, h2⟩
      by_contra hne
      have hpos : 0 < ‖(χ g : ℚ_[l]) - 1‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        exact fun e => hne (Units.ext e)
      obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hpos
      exact absurd ((h.fix_iff g m).1 fun ζ hζ => h2 ζ ⟨m, hζ⟩) (not_le.2 hm)
    · intro h1
      refine ⟨hg, ?_⟩
      rintro x ⟨m, hx⟩
      refine (h.fix_iff g m).2 ?_ x hx
      rw [h1, Units.val_one, sub_self, norm_zero]
      positivity
end GlobalTheory.Cyc
