-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_monomial_basis_of_abByP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:22:02.750831+00:00
-- url     : https://prove2.me/submissions/ed9c6ef3-7565-4d6f-b9f8-1dd24eaef342

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsAbelianByPrimePowerGroupSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantEqTopOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisOfImprimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisAbelianByPrimePower
import Theorems.Thm_GlobalTheory_CuspGL_exists_monomial_basis_of_isCompl
import Theorems.Thm_GlobalTheory_BI_AbByP_subgroup
import Theorems.Thm_GlobalTheory_BI_finrank_eq_one_or_imprimitive
import Theorems.Thm_GlobalTheory_CuspGL_exists_monomial_basis_of_imprimitive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → (Nat.card G : k) ≠ 0 → ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n), ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  intro k _
  have key : ∀ (m : ℕ) (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k],
      Nat.card G + Module.finrank k V = m → AbByP G → (Nat.card G : k) ≠ 0 →
      ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
        ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro G _ _ V _ _ _ ρ _ hm hG hcard
    by_cases h0 : Module.finrank k V = 0
    · exact ⟨0, Module.finBasisOfFinrankEq k V h0, fun g i => i.elim0⟩
    by_cases hirr : ρ.IsIrreducible
    · rcases finrank_eq_one_or_imprimitive k G V ρ hG hirr with h1 | ⟨T, W, hT, hW, hind, hsup⟩
      · let b := Module.finBasisOfFinrankEq k V h1
        refine ⟨1, b, fun g i => ⟨0, b.repr (ρ g (b i)) 0, ?_⟩⟩
        have := b.sum_repr (ρ g (b i))
        rw [Fin.sum_univ_one] at this
        exact this.symm
      · refine exists_monomial_basis_of_imprimitive k G V ρ T W hind hsup ?_
        let σ : Subrepresentation (ρ.comp T.subtype : Representation k T V) :=
          ⟨W, fun t w hw => hW t t.2 w hw⟩
        have hlt : Nat.card T < Nat.card G := by
          have := T.card_le_card_group
          have h2 : Nat.card T ≠ Nat.card G := fun H => hT (Subgroup.eq_top_of_card_eq T H)
          omega
        have hle : Module.finrank k W ≤ Module.finrank k V := Submodule.finrank_le W
        have hc : (Nat.card T : k) ≠ 0 := by
          intro H
          obtain ⟨d, hd⟩ := T.card_subgroup_dvd_card
          apply hcard
          rw [hd, Nat.cast_mul, H, zero_mul]
        obtain ⟨n, b, hb⟩ := ih _ (by omega) T W σ.toRepresentation rfl (AbByP.subgroup G T hG) hc
        refine ⟨n, b, fun t ht i => ?_⟩
        obtain ⟨j, c, hj⟩ := hb ⟨t, ht⟩ i
        exact ⟨j, c, congrArg Subtype.val hj⟩
    · haveI : NeZero (Nat.card G : k) := ⟨hcard⟩
      haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h0)
      haveI : Nontrivial (Subrepresentation ρ) :=
        ⟨⊥, ⊤, fun H => (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤)
          (congrArg Subrepresentation.toSubmodule H)⟩
      have hex : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
        by_contra H
        push Not at H
        exact hirr ⟨fun U => by
          by_cases hU : U = ⊥
          · exact Or.inl hU
          · exact Or.inr (H U hU)⟩
      obtain ⟨U, hU0, hU1⟩ := hex
      obtain ⟨U', hUU'⟩ := exists_isCompl U
      have hcompl : IsCompl U.toSubmodule U'.toSubmodule :=
        ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.inf_eq_bot),
          codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.sup_eq_top)⟩
      have hsub : ∀ S : Subrepresentation ρ, S ≠ ⊤ →
          ∃ (n : ℕ) (b : Module.Basis (Fin n) k S.toSubmodule), ∀ (g : G) (i : Fin n),
            ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V) := by
        intro S hS
        have hlt : Module.finrank k S.toSubmodule < Module.finrank k V :=
          Submodule.finrank_lt (fun H => hS (Subrepresentation.ext H))
        obtain ⟨n, b, hb⟩ := ih _ (by omega) G S.toSubmodule S.toRepresentation rfl hG hcard
        refine ⟨n, b, fun g i => ?_⟩
        obtain ⟨j, c, hj⟩ := hb g i
        exact ⟨j, c, congrArg Subtype.val hj⟩
      refine exists_monomial_basis_of_isCompl ρ _ _ hcompl (hsub U hU1) (hsub U' ?_)
      rintro rfl
      exact hU0 (by simpa using hUU'.inf_eq_bot)
  intro G _ _ V _ _ _ ρ _ hG hc
  exact key _ G V ρ rfl hG hc
end GlobalTheory.CuspGL
