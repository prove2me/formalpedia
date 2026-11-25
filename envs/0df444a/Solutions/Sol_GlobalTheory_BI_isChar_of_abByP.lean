-- Prove2me | solution 1 for GlobalTheory.BI.isChar_of_abByP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:32:24.653104+00:00
-- url     : https://prove2.me/submissions/609ef75b-cdb9-4156-9fd2-22c4ea4e88ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsAbelianByPrimePowerGroupSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldZeroAndAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrimStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldLinearOfPrimitiveRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldAbelianByPrimePower
import Theorems.Thm_GlobalTheory_T_irreducibleCharacter_linear_or_induced_abelianByPrimePower
import Theorems.Thm_GlobalTheory_T_isAbelianByPrimePowerGroup_subgroup
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_inducedClassFunction
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_induction_irreducible
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_linear_of_primitiveRoot
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_zero_and_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ
  have key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → (∀ g : G, g ^ m = 1) → AbByP G →
      ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hn hG hA χ hχ
      refine GlobalTheory.T.isCharacterOverSubfield_induction_irreducible L L G (fun a => IsChar K L a) (GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G).1 ?_ χ hχ
      intro φ c hφ _ hc
      refine (GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G).2 φ c ?_ hc
      rcases GlobalTheory.T.irreducibleCharacter_linear_or_induced_abelianByPrimePower L G φ hA hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have : φ = fun g => (lam g : L) := funext hlam
        rw [this]
        exact GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot K L G m ζ lam hm hζ hG
      · have hlt : Nat.card T < n := by
          rw [← hn]
          exact lt_of_le_of_ne (Subgroup.card_le_card_group T)
            (fun h => hT (Subgroup.eq_top_of_card_eq T h))
        refine GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction K L G T ψ (ih _ hlt T rfl ?_ (GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup G T hA) ψ hψ)
        intro g
        exact Subtype.ext (by simpa using hG g)
  intro G _ _
  exact key _ G rfl
end GlobalTheory.BI
