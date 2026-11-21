-- Prove2me | solution 1 for JardenShami.exists_closed_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:43.359159+00:00
-- url     : https://prove2.me/submissions/9babd469-40eb-43c2-b1eb-18a0aec5cd4b

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_Kappa_exists_gt
import Theorems.Thm_JardenShami_Kappa_coe_le_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_lt
import Theorems.Thm_JardenShami_Kappa_mk_Iic_lt
import Theorems.Thm_JardenShami_Kappa_mk_eq
attribute [local simp] JardenShami.Kappa.coe_mk



set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {κ ρ : Cardinal.{w}} (hκ : κ.IsRegular) (hρ : ρ.IsRegular)
    (hρκ : ρ < κ) {α₀ : Ordinal.{w}} (hα₀ : α₀ < κ.ord) (σ : Ordinal.{w} → Ordinal.{w})
    (hσ : ∀ q < κ.ord, σ q < κ.ord) :
    ∃ α, α₀ < α ∧ α < κ.ord ∧ (∀ q < α, σ q < α) ∧
      ∀ (ι : Type w) (f : ι → Ordinal.{w}), #ι < ρ → (∀ i, f i < α) → ∃ q < α, ∀ i, f i ≤ q := by
  classical
  have hκ0 := hκ.aleph0_le
  have hlim : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ0
  have hcof : κ.ord.cof = κ := hκ.cof_ord
  -- `σ' x = max x (sup_{q ≤ x} σ q)`
  let σ' : Ordinal.{w} → Ordinal.{w} := fun x =>
    max x (⨆ q : {q : Kappa κ // (q : Ordinal.{w}) ≤ x}, σ q.1)
  have hσ'lt : ∀ x < κ.ord, σ' x < κ.ord := by
    intro x hx
    refine max_lt hx (Ordinal.iSup_lt_of_lt_cof ?_ fun q => hσ _ (Kappa.coe_lt_ord _))
    rw [hcof]
    refine (Cardinal.mk_le_of_injective (f := fun q : {q : Kappa κ // (q : Ordinal.{w}) ≤ x} =>
      (⟨q.1, by rw [Set.mem_Iic, ← Kappa.coe_le_coe, Kappa.coe_mk]; exact q.2⟩ :
        Set.Iic (Kappa.mk x hx))) ?_).trans_lt (Kappa.mk_Iic_lt hκ0 _)
    intro a b h
    exact Subtype.ext (congrArg (fun z : Set.Iic (Kappa.mk x hx) => (z : Kappa κ)) h)
  have hσ'ge : ∀ x q, q ≤ x → q < κ.ord → σ q ≤ σ' x := fun x q hqx hq =>
    (Ordinal.le_iSup (fun q : {q : Kappa κ // (q : Ordinal.{w}) ≤ x} => σ q.1)
      ⟨Kappa.mk q hq, by rw [Kappa.coe_mk]; exact hqx⟩ |>.trans_eq' (by rw [Kappa.coe_mk])).trans
      (le_max_right _ _)
  -- the recursion `g i = max (α₀ + 1) (sup_{j<i} σ' (g j) + 1)`
  obtain ⟨g, hg⟩ : ∃ g : Kappa ρ → Ordinal.{w}, ∀ i,
      g i = max (α₀ + 1) (⨆ j : Set.Iio i, (σ' (g j) + 1)) :=
    ⟨wellFounded_lt.fix fun i ih => max (α₀ + 1) (⨆ j : Set.Iio i, (σ' (ih j j.2) + 1)),
      fun i => by rw [WellFounded.fix_eq]⟩
  have hgstep : ∀ i, ∀ j < i, σ' (g j) + 1 ≤ g i := fun i j hj => by
    rw [hg i]
    exact (Ordinal.le_iSup (fun j : Set.Iio i => σ' (g j) + 1) ⟨j, hj⟩).trans (le_max_right _ _)
  have hgmono : ∀ i j, j < i → g j < g i := fun i j hj =>
    (Order.lt_add_one_iff.2 (le_max_left _ _)).trans_le (hgstep i j hj)
  have hglt : ∀ i, g i < κ.ord := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i IH =>
    rw [hg i]
    refine max_lt (hlim.add_one_lt hα₀) (Ordinal.iSup_lt_of_lt_cof ?_ fun j =>
      hlim.add_one_lt (hσ'lt _ (IH j j.2)))
    rw [hcof]
    have := Cardinal.mk_Iio_lt i (by rw [Kappa.mk_eq, Ordinal.type_toType])
    rw [Kappa.mk_eq] at this
    exact this.trans hρκ
  have hρ0 := hρ.aleph0_le
  have : Nonempty (Kappa ρ) := ⟨Kappa.mk 0 (Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hρ0))⟩
  refine ⟨⨆ i, g i, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i⟩ := this
    have h1 : α₀ + 1 ≤ g i := by rw [hg i]; exact le_max_left _ _
    exact (Order.lt_add_one_iff.2 le_rfl).trans_le (h1.trans (Ordinal.le_iSup g i))
  · exact Ordinal.iSup_lt_of_lt_cof (by rw [hcof, Kappa.mk_eq]; exact hρκ) hglt
  · intro q hq
    obtain ⟨i, hi⟩ := Ordinal.lt_iSup_iff.1 hq
    obtain ⟨i', hi'⟩ := Kappa.exists_gt hρ0 i
    have hqκ : q < κ.ord := hi.trans (hglt i)
    calc σ q ≤ σ' (g i) := hσ'ge _ _ hi.le hqκ
      _ < σ' (g i) + 1 := Order.lt_add_one_iff.2 le_rfl
      _ ≤ g i' := hgstep i' i hi'
      _ ≤ ⨆ i, g i := Ordinal.le_iSup g i'
  · intro ι f hι hf
    have hex : ∀ k, ∃ i, f k < g i := fun k => Ordinal.lt_iSup_iff.1 (hf k)
    choose ik hik using hex
    obtain ⟨is, his⟩ := Kappa.exists_gt_of_card_lt hρ
      (Cardinal.mk_range_le.trans_lt hι : #(Set.range ik) < ρ)
    obtain ⟨is', his'⟩ := Kappa.exists_gt hρ0 is
    exact ⟨g is, (hgmono is' is his').trans_le (Ordinal.le_iSup g is'),
      fun k => ((hik k).trans (hgmono is (ik k) (his _ ⟨k, rfl⟩))).le⟩
end JardenShami
