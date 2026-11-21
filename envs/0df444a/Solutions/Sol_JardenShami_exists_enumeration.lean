-- Prove2me | solution 1 for JardenShami.exists_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:11.20274+00:00
-- url     : https://prove2.me/submissions/99363b2d-4191-451a-9954-bf53c3ce264d

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Tree_lev_nonempty
import Theorems.Thm_JardenShami_exists_bijOn_ord


set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
    (hκ : κ ≠ 0) (hT : IsKappaTree κ T) : Nonempty (Enumeration κ T) := by
  classical
  have hκ0 : (0 : Ordinal.{w}) < κ.ord := Cardinal.ord_pos.2 (pos_iff_ne_zero.2 hκ)
  obtain ⟨t₀, -⟩ := lev_nonempty (hT.1 ▸ hκ0 : (0 : Ordinal.{w}) < height T)
  have hf : ∀ α : Ordinal.{w}, ∃ f : Ordinal.{w} → T, ∀ _ : α < κ.ord,
      Set.BijOn f (Set.Iio (#(Lev T α)).ord) (Lev T α) := by
    intro α
    by_cases hα : α < κ.ord
    · obtain ⟨c, hc⟩ := lev_nonempty (hT.1 ▸ hα : α < height T)
      obtain ⟨f, hf, -⟩ := exists_bijOn_ord hc
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => t₀, fun h => absurd h hα⟩
  choose tf htf using hf
  exact ⟨⟨tf, htf⟩⟩
end JardenShami
