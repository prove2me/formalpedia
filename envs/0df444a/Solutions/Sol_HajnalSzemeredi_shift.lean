-- Prove2me | solution 1 for HajnalSzemeredi.shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:36.944796+00:00
-- url     : https://prove2.me/submissions/762feea6-8096-4d58-a475-7c5f2d8a4e89

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Definitions.Def_HajnalSzemeredi_Reach
public import Definitions.Def_HajnalSzemeredi_Shift
public import Theorems.Thm_HajnalSzemeredi_mem_palette_of_reach
public import Theorems.Thm_HajnalSzemeredi_card_cls_update_old
public import Theorems.Thm_HajnalSzemeredi_card_cls_update_self
public import Theorems.Thm_HajnalSzemeredi_cls_update_other
public import Theorems.Thm_HajnalSzemeredi_exists_step_avoid
public import Theorems.Thm_HajnalSzemeredi_into_update
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_proper_update
public import Theorems.Thm_HajnalSzemeredi_transfer
attribute [local simp] HajnalSzemeredi.mem_cls



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution {S : Finset V} {P : Finset ℕ} {s lo : ℕ} (K : Finset ℕ) :
    ∀ (c : V → ℕ) (hi : ℕ), IsNear G S P c s lo hi →
      ReflTransGen (fun a b => Mov G S c a b ∧ a ∈ K ∧ b ∈ K) hi lo →
      ∃ c', IsEq G S P c' s := by
  induction K using Finset.strongInduction with
  | H K ih =>
  intro c hi hc hpath
  obtain ⟨j, ⟨⟨v, hv, hmov⟩, hiK, hjK⟩, hjhi, hjpath⟩ :=
    exists_step_avoid hpath (Ne.symm hc.lo_ne_hi)
  rw [mem_cls] at hv
  obtain ⟨hvS, hvc⟩ := hv
  have hcvj : c v ≠ j := hvc ▸ Ne.symm hjhi
  set c' := Function.update c v j with hc'
  have hproper : Proper G S c' := proper_update hc.proper hmov
  -- tamaños tras el movimiento
  have hcard_j : (cls S c' j).card = (cls S c j).card + 1 := card_cls_update_self hvS hcvj
  have hcard_hi : (cls S c' hi).card + 1 = (cls S c hi).card := by
    have := card_cls_update_old (j := j) hvS hcvj
    rwa [hvc] at this
  have hcard_other : ∀ k, k ≠ j → k ≠ hi → (cls S c' k).card = (cls S c k).card := by
    intro k hkj hkhi
    rw [cls_update_other hkj (hvc ▸ hkhi)]
  by_cases hjlo : j = lo
  · -- llegamos a la clase pequeña: la coloración es equitativa
    subst hjlo
    refine ⟨c', hproper, into_update hc.into hc.lo_mem, fun k hk => ?_⟩
    by_cases hkj : k = j
    · subst hkj; rw [hcard_j, hc.card_lo]
    · by_cases hkhi : k = hi
      · subst hkhi; have := hc.card_hi; omega
      · rw [hcard_other k hkj hkhi, hc.card k hk hkj hkhi]
  · -- `j` pasa a ser la clase grande; el camino restante evita `hi`
    have hjP : j ∈ P := mem_palette_of_reach hc.into (fun a b h => h.1.1) hjpath hjlo
    have hlohi : lo ≠ hi := hc.lo_ne_hi
    have hnear : IsNear G S P c' s lo j := by
      refine ⟨hproper, into_update hc.into hjP, hc.lo_mem, hjP, Ne.symm hjlo, ?_, ?_, ?_⟩
      · rw [hcard_other lo (Ne.symm hjlo) hlohi, hc.card_lo]
      · rw [hcard_j, hc.card j hjP hjlo hjhi]
      · intro k hk hklo hkj
        by_cases hkhi : k = hi
        · subst hkhi; have := hc.card_hi; omega
        · rw [hcard_other k hkj hkhi, hc.card k hk hklo hkhi]
    refine ih (K.erase hi) (erase_ssubset hiK) c' j hnear ?_
    refine transfer hjpath fun a b hab hbj => ?_
    obtain ⟨⟨⟨w, hw, hwmov⟩, haK, hbK⟩, hahi, hbhi⟩ := hab
    rw [mem_cls] at hw
    have hwv : w ≠ v := by
      rintro rfl
      exact hahi (hw.2.symm.trans hvc)
    refine ⟨⟨w, ?_, ?_⟩, mem_erase.mpr ⟨hahi, haK⟩, mem_erase.mpr ⟨hbhi, hbK⟩⟩
    · rw [mem_cls, hc', Function.update_of_ne hwv]
      exact hw
    · intro u hu
      rw [cls_update_other hbj (hvc ▸ hbhi)] at hu
      exact hwmov u hu
end HajnalSzemeredi
