-- Prove2me | solution 1 for GlobalTheory.DualTransfer.exists_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:44:29.418215+00:00
-- url     : https://prove2.me/submissions/b18d34ab-9b92-4a17-981d-07f40f3157bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DivisiblePontryaginAnnihilatorDuality
import Theorems.Thm_GlobalTheory_DualTransfer_exists_hom
import Theorems.Thm_GlobalTheory_DualTransfer_card_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DualTransfer
namespace GlobalTheory.DualTransfer
theorem _root_.solution {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (h1 : ∀ a a' b, e (a + a') b = e a b * e a' b) (h2 : ∀ a b b', e a (b + b') = e a b * e a b')
    (h3 : ∀ b, e 0 b = 1) (h4 : ∀ a, e a 0 = 1) (M : AddSubgroup A) (K : AddSubgroup B)
    [Finite (A ⧸ M)] [Finite (B ⧸ K)]
    (hM : ∀ a, a ∈ M ↔ ∀ b, e a b = 1) (hK : ∀ b, b ∈ K ↔ ∀ a, e a b = 1)
    (H : AddSubgroup A) (hMH : M ≤ H) (x : A) (hx : x ∉ H) :
    ∃ b, (∀ u ∈ H, e u b = 1) ∧ e x b ≠ 1 := by
  classical
  obtain ⟨f, hf⟩ := exists_hom e h1 h2 h3 h4 M (fun a ha b => (hM a).mp ha b)
  obtain ⟨f', hf'⟩ := exists_hom (fun b a => e a b) (fun b b' a => h2 a b b')
    (fun b a a' => h1 a a' b) (fun b => h4 b) (fun a => h3 a) K (fun b hb a => (hK b).mp hb a)
  have c1 := card_range e M K hK f hf
  have c2 := card_range (fun b a => e a b) K M hM f' hf'
  have : Fintype (A ⧸ M) := Fintype.ofFinite _
  have : Fintype (B ⧸ K) := Fintype.ofFinite _
  have cA : Nat.card (AddChar (A ⧸ M) ℂ) = Nat.card (A ⧸ M) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have cB : Nat.card (AddChar (B ⧸ K) ℂ) = Nat.card (B ⧸ K) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have le1 : Nat.card f.range ≤ Nat.card (AddChar (A ⧸ M) ℂ) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have le2 : Nat.card f'.range ≤ Nat.card (AddChar (B ⧸ K) ℂ) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have htop : f.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by omega)
  set r := QuotientAddGroup.map M H (AddMonoidHom.id A) (fun a ha => hMH ha) with hr
  have : Finite (A ⧸ H) := Finite.of_surjective r (fun q => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨(a : A ⧸ M), rfl⟩)
  have hx0 : (x : A ⧸ H) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨ψ0, hψ0⟩ := AddChar.exists_apply_ne_zero.mpr hx0
  have hmem : ψ0.compAddMonoidHom r ∈ f.range := by
    rw [htop]
    exact AddSubgroup.mem_top _
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, fun u hu => ?_, ?_⟩
  · rw [← hf b u, hb, AddChar.compAddMonoidHom_apply]
    have hu0 : (u : A ⧸ H) = 0 := (QuotientAddGroup.eq_zero_iff u).mpr hu
    show ψ0 (u : A ⧸ H) = 1
    rw [hu0]
    exact ψ0.map_zero_eq_one
  · rw [← hf b x, hb, AddChar.compAddMonoidHom_apply]
    exact hψ0
end GlobalTheory.DualTransfer
