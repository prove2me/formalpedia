-- Prove2me | solution 1 for GroundTheory.LocalField.exists_isPrimitiveRoot_card_residueField_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:46.133658+00:00
-- url     : https://prove2.me/submissions/858eacc5-8a9e-4767-83f7-d935e7b0f340

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Theorems.Thm_GroundTheory_LocalField_exists_pow_eq_one_residue_eq

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
open ValuativeRel Polynomial
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    ∃ ζ : 𝒪[L], IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := 𝓀[L]ˣ)
  have hpg : IsPrimitiveRoot (g : 𝓀[L]) (Nat.card 𝓀[L] - 1) := by
    rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  obtain ⟨x, hx, hxg⟩ :=
    exists_pow_eq_one_residue_eq (natCast_card_residueField_sub_one_ne_zero L) hpg.pow_eq_one
  refine ⟨x, hx, fun l hl ↦ hpg.dvd_of_pow_eq_one l ?_⟩
  rw [← hxg, ← map_pow, hl, map_one]
end GroundTheory.LocalField
