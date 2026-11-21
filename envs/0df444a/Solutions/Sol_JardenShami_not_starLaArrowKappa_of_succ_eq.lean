-- Prove2me | solution 1 for JardenShami.not_starLaArrowKappa_of_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:52.956162+00:00
-- url     : https://prove2.me/submissions/25f53999-7dd2-4901-b378-0579effb54f2

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_isStarLocallyAdditive_iff
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_eq
import Theorems.Thm_JardenShami_Kappa_mk_coe
import Theorems.Thm_JardenShami_Kappa_mk_eq
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ = κ) : ¬ StarLaArrowKappa κ μ := by
  classical
  have hκ0 := hκ.aleph0_le
  -- `μ` is infinite
  have hμ : ℵ₀ ≤ μ := by
    by_contra hc
    obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.1 (lt_of_not_ge hc)
    rw [← h, Cardinal.succ_natCast, ← Nat.cast_succ] at hκ0
    exact Cardinal.natCast_lt_aleph0.not_ge hκ0
  have : Nonempty (Kappa μ) := by
    rw [← Cardinal.mk_ne_zero_iff, Kappa.mk_eq]
    exact (Cardinal.aleph0_pos.trans_le hμ).ne'
  -- for each `α`, a map `g α : κ → μ`, injective on `{β : β < α}`
  have hg : ∀ α : Kappa κ, ∃ g : Kappa κ → Kappa μ, Set.InjOn g (Set.Iio α) := by
    intro α
    have hlt : #(Set.Iio α) < κ := by
      have := Cardinal.mk_Iio_lt α (by rw [Kappa.mk_eq, Ordinal.type_toType])
      rwa [Kappa.mk_eq] at this
    replace hlt : #(Set.Iio α) ≤ μ := Order.lt_succ_iff.1 (hlt.trans_eq h.symm)
    obtain ⟨e⟩ : Nonempty (Set.Iio α ↪ Kappa μ) := by
      rw [← Cardinal.le_def, Kappa.mk_eq]
      exact hlt
    refine ⟨fun β => if hβ : β < α then e ⟨β, hβ⟩ else Classical.arbitrary _, ?_⟩
    intro β hβ β' hβ' he
    simp only [dif_pos (show β < α from hβ),
      dif_pos (show β' < α from hβ')] at he
    exact congrArg Subtype.val (e.injective he)
  choose g hg using hg
  let C : Coloring (Kappa κ) (Kappa μ) := fun p => g p.1.sup p.1.inf
  have hCc : ∀ (a b : Kappa κ) (hab : a < b), C.color a b hab = g b a := by
    intro a b hab
    change g (Sym2.sup s(a, b)) (Sym2.inf s(a, b)) = g b a
    rw [Sym2.sup_mk, Sym2.inf_mk, sup_of_le_right hab.le, inf_of_le_left hab.le]
  -- `C(β,α) ≠ C(γ,α)` for `β < γ < α`
  have hne : ∀ (β γ α : Kappa κ) (hβγ : β < γ) (hγα : γ < α),
      C.color β α (hβγ.trans hγα) ≠ C.color γ α hγα := by
    intro β γ α hβγ hγα e
    rw [hCc, hCc] at e
    exact hβγ.ne (hg α (hβγ.trans hγα) hγα e)
  intro hArrow
  have hstar : IsStarLocallyAdditive C := by
    rw [isStarLocallyAdditive_iff]
    intro x y z w hxy hyz hzw e
    exact absurd e.symm (hne x y z hxy hyz)
  obtain ⟨H, hH, hHom⟩ := hArrow C hstar
  -- three elements `x < y < z` of `H`
  obtain ⟨x, hx⟩ : H.Nonempty := by
    rw [← Set.nonempty_coe_sort, ← Cardinal.mk_ne_zero_iff, hH]
    exact (Cardinal.aleph0_pos.trans_le hκ0).ne'
  obtain ⟨y, hy, hxy⟩ := Kappa.exists_gt_of_card_eq hκ0 hH x
  obtain ⟨z, hz, hyz⟩ := Kappa.exists_gt_of_card_eq hκ0 hH y
  refine hne x y z hxy hyz (hHom _ _ ?_ ?_)
  · intro u hu
    rcases Sym2.mem_iff.1 hu with rfl | rfl
    · exact hx
    · exact hz
  · intro u hu
    rcases Sym2.mem_iff.1 hu with rfl | rfl
    · exact hy
    · exact hz
end JardenShami
