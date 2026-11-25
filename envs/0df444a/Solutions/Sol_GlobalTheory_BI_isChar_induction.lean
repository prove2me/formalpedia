-- Prove2me | solution 1 for GlobalTheory.BI.isChar_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:12:48.475224+00:00
-- url     : https://prove2.me/submissions/7e6df5cc-849d-4e35-befb-9f6e908e2dc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIrrCharAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducible
import Theorems.Thm_GlobalTheory_BI_exists_irrChar_add


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
namespace _root_.GlobalTheory.BI
theorem _root_.solution :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G]
      [Finite G] (Q : (G → L) → Prop), Q 0 →
      (∀ φ c : G → L, _root_.GlobalTheory.BI.IsIrrChar K L φ → _root_.GlobalTheory.BI.IsChar K L c →
        Q c → Q (φ + c)) → ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → Q a := by
  intro K L _ _ _ _ _ G _ _ Q h0 hstep
  have hchar : ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → ∃ n : ℕ, a 1 = n := by
    intro a ha
    unfold _root_.GlobalTheory.BI.IsChar at ha
    obtain ⟨n, ρ, hρ⟩ := ha
    exact ⟨n, by rw [hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩
  have hirr : ∀ φ : G → L, _root_.GlobalTheory.BI.IsIrrChar K L φ →
      ∃ m : ℕ, 0 < m ∧ φ 1 = m := by
    intro φ hφ
    unfold _root_.GlobalTheory.BI.IsIrrChar at hφ
    obtain ⟨m, ρ, hρirr, hρ⟩ := hφ
    refine ⟨m, Nat.pos_of_ne_zero fun hm => ?_, by
      rw [hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩
    subst hm
    have hs : IsSimpleOrder (Subrepresentation ρ) := hρirr
    obtain ⟨x, y, hxy⟩ := hs.toNontrivial.exists_pair_ne
    apply hxy
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => y.toSubmodule.zero_mem, fun _ => x.toSubmodule.zero_mem⟩
  have key : ∀ n : ℕ, ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a 1 = n → Q a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha ha1
      by_cases hz : a = 0
      · rw [hz]; exact h0
      obtain ⟨φ, c, hφ, hc, rfl⟩ := _root_.GlobalTheory.BI.exists_irrChar_add K L G a ha hz
      obtain ⟨m, hm, hφ1⟩ := hirr φ hφ
      obtain ⟨k, hk1⟩ := hchar c hc
      have hn : n = m + k := by
        have hsum : ((m + k : ℕ) : L) = n := by
          rw [Nat.cast_add, ← hφ1, ← hk1]
          exact ha1
        exact_mod_cast hsum.symm
      exact hstep φ c hφ hc (ih k (by omega) c hc hk1)
  intro a ha
  obtain ⟨n, hn⟩ := hchar a ha
  exact key n a ha hn
end _root_.GlobalTheory.BI
end GlobalTheory.BI
