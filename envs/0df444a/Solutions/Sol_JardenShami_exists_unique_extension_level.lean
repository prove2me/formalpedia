-- Prove2me | solution 1 for JardenShami.exists_unique_extension_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:00.99441+00:00
-- url     : https://prove2.me/submissions/e67315c4-45c4-4455-8196-96a8f7b239e2

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_le_mk_lev_of_splitting

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ lam : Cardinal.{w})
    (hlamreg : lam.IsRegular) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hwp : WellPruned T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∀ α : Ordinal.{w}, α < κ.ord → α.cof = lam →
      ∃ q < α, ∀ β : Ordinal.{w}, q < β → β < α →
        ∀ a ∈ Lev T q, ∀ b ∈ Lev T β, ∀ c ∈ Lev T β, a < b → a < c → b = c := by
  intro α hα hcof
  by_contra hc
  push Not at hc
  have hα0 : (0 : Ordinal.{w}) < α := by
    rw [pos_iff_ne_zero]
    rintro rfl
    rw [Ordinal.cof_zero] at hcof
    exact hlamreg.pos.ne' hcof.symm
  have hle := le_mk_lev_of_splitting (ρ := lam) (α₀ := 0)
    (fun x hx => hwp.2 x α hx (by rw [hT.1]; exact hα))
    (fun ι f hι hf => ⟨⨆ i, f i, Ordinal.iSup_lt_of_lt_cof (by rwa [hcof]) hf,
      fun i => Ordinal.le_iSup f i⟩)
    hα0
    (fun q _ hq => by
      obtain ⟨β, hqβ, hβα, a, ha, b, hb, c, hc', hab, hac, hbc⟩ := hc q hq
      exact ⟨a, b, c, ha, by rw [hb]; exact hqβ, by rw [hb]; exact hβα, hc'.trans hb.symm,
        hab, hac, hbc⟩)
  exact (hle.trans_lt (hlev α)).false
end JardenShami
