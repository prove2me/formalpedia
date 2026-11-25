-- Prove2me | solution 1 for GlobalTheory.SemilinearNullity.rank_nullity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:00:57.244856+00:00
-- url     : https://prove2.me/submissions/c239966a-35c3-4a64-afae-b3967d2fd9d8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdeal
import Theorems.Thm_GlobalTheory_SemilinearNullity_mm_zero
import Theorems.Thm_GlobalTheory_SemilinearNullity_ge_of_pow
import Theorems.Thm_GlobalTheory_SemilinearNullity_IndepOn_indepMod
import Theorems.Thm_GlobalTheory_SemilinearNullity_exists_relation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.SemilinearNullity
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.SemilinearNullity
theorem _root_.solution : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) (m k Q : ℕ), 1 ≤ Q → ∀ Y : Fin m → σ → C, (∀ δ x, V.Ge 0 (Y δ x)) → (∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν s, V.MM (∑ δ, x ν δ ^ Q * Y δ s)) → N ≤ k) → ∃ (m' : ℕ) (cc : Fin m' ↪ Fin m), m ≤ m' + k ∧ IndepMod V (fun ν => Y (cc ν)) := by
  intro C _ _ V σ m k Q hQ Y hY hk
  have hQ0 : Q ≠ 0 := by omega
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun T : Finset (Fin m) => IndepOn V Y T) Finset.card
    ⟨∅, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro c _ h0 _ δ
      rw [h0 δ (by simp)]
      exact mm_zero⟩
  have hT' : IndepOn V Y T := (Finset.mem_filter.1 hT).2
  have hn : ∀ δ, δ ∉ T → ¬ IndepOn V Y (insert δ T) := fun δ hδ h => by
    have := hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [Finset.card_insert_of_notMem hδ] at this
    omega
  have hrt : ∀ a : C, ∃ z : C, z ^ Q = a ∧ (a = 1 → z = 1) ∧ (a = 0 → z = 0) := by
    intro a
    by_cases h : a = 1
    · exact ⟨1, by simp [h], fun _ => rfl, fun h0 => absurd (h.symm.trans h0) one_ne_zero⟩
    · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a (Nat.pos_of_ne_zero hQ0)
      exact ⟨z, hz, fun h1 => absurd h1 h, fun h0 => pow_eq_zero_iff hQ0 |>.mp (hz.trans h0)⟩
  choose rt hrt hrt1 hrt0 using hrt
  let e : Fin Tᶜ.card ↪ Fin m := (Tᶜ.orderEmbOfFin rfl).toEmbedding
  have he : ∀ ν, e ν ∉ T := fun ν => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ rfl ν)
  choose r hr hr1 hr0 hrs using fun ν => exists_relation hY hT' (hn _ (he ν))
  have hle := hk Tᶜ.card (fun ν δ => rt (r ν δ))
    (fun ν δ => ge_of_pow hQ0 (by rw [hrt]; exact hr ν δ))
    (fun c _ hs ν => by
      have h1 : V.MM (∑ b, c b * rt (r b (e ν))) := hs (e ν)
      rw [Finset.sum_eq_single ν (fun b _ hb => by
        rw [hrt0 _ (hr0 b _ (he ν) (fun h => hb (e.injective h).symm)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h), hrt1 _ (hr1 ν), mul_one] at h1
      exact h1)
    (fun ν s => by simp only [hrt]; exact hrs ν s)
  refine ⟨T.card, (T.orderEmbOfFin rfl).toEmbedding, ?_,
    hT'.indepMod _ fun ν => Finset.orderEmbOfFin_mem _ rfl ν⟩
  rw [Finset.card_compl, Fintype.card_fin] at hle
  omega
end GlobalTheory.SemilinearNullity
