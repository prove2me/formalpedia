-- Prove2me | solution 1 for JardenShami.isWeaklyCompact_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:49:16.27671+00:00
-- url     : https://prove2.me/submissions/22e2beb0-cfb5-41c1-a04b-6f33165e60d0

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_treeExp_lt_iff_isInaccessible

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ : Cardinal.{w}) (hunc : ℵ₀ < κ) :
    IsWeaklyCompact κ ↔
      κ.IsRegular ∧ NoAronszajn κ ∧
        ∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ := by
  constructor
  · rintro ⟨hκ, htp⟩
    exact ⟨hκ.isRegular, htp,
      (treeExp_lt_iff_isInaccessible κ hunc hκ.isRegular).2 hκ⟩
  · rintro ⟨hreg, htp, h⟩
    exact ⟨(treeExp_lt_iff_isInaccessible κ hunc hreg).1 h, htp⟩
end JardenShami
