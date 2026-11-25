-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramifiedSubextension.le_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:32.28424+00:00
-- url     : https://prove2.me/submissions/f5677292-5d55-4b1f-ace1-5ac9213b7ad0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Theorems.Thm_GroundTheory_LocalField_pow_sub_one_dvd_pow_sub_one
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_eq_adjoin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
variable [HasUnramifiedRoots K Ω]
namespace GroundTheory.LocalField
namespace IsUnramifiedSubextension
theorem _root_.solution {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hn : n ≠ 0) (hdvd : Module.finrank K E ∣ n) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E ≤ K⟮ζ⟯ := by
  have := hE.1
  have hm : Module.finrank K E ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨ξ, hξ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hm
  rw [hE.eq_adjoin rfl hm hξ, adjoin_simple_le_iff]
  have hξn : ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1 := by
    obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hdvd
    rw [hc, pow_mul, hξ.pow_eq_one, one_pow]
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) :=
    ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξn
  exact pow_mem (mem_adjoin_simple_self K ζ) i
end IsUnramifiedSubextension
end GroundTheory.LocalField
