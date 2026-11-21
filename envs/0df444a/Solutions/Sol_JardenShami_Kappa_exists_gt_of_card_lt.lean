-- Prove2me | solution 1 for JardenShami.Kappa.exists_gt_of_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:36.234688+00:00
-- url     : https://prove2.me/submissions/2ca185d5-8807-4252-9486-84b598876851

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}
namespace JardenShami
namespace Kappa
theorem _root_.solution (hκ : κ.IsRegular) {S : Set (Kappa κ)} (hS : #S < κ) :
    ∃ x, ∀ y ∈ S, y < x := by
  by_contra h
  have hc : IsCofinal S := by
    by_contra h'
    exact h (not_isCofinal_iff.1 h')
  have := Order.cof_le hc
  rw [Ordinal.cof_toType, hκ.cof_ord] at this
  exact this.not_gt hS
end Kappa
end JardenShami
