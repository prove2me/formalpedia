-- Prove2me | solution 1 for GlobalTheory.Nef.exists_fin_enum_multiset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:05:13.586346+00:00
-- url     : https://prove2.me/submissions/536ca144-4866-46ea-939b-8869d14b6896

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BinaryFormSplits
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution {α : Type} : ∀ (n : ℕ) (M : Multiset α), Multiset.card M = n →
    ∃ u : Fin n → α, Multiset.map u Finset.univ.val = M := by
  classical
  intro n
  induction n with
  | zero =>
    intro M hM
    refine ⟨Fin.elim0, ?_⟩
    rw [Multiset.card_eq_zero] at hM
    subst hM; simp
  | succ n ih =>
    intro M hM
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card M)
    obtain ⟨u, hu⟩ := ih (M.erase a) (by rw [Multiset.card_erase_of_mem ha, hM]; rfl)
    refine ⟨Fin.cons a u, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Multiset.cons_coe, ← Fin.univ_val_map, hu, Multiset.cons_erase ha]
end GlobalTheory.Nef
