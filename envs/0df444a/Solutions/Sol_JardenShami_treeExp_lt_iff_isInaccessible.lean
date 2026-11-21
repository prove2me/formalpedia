-- Prove2me | solution 1 for JardenShami.treeExp_lt_iff_isInaccessible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:41.024498+00:00
-- url     : https://prove2.me/submissions/f9841f46-d4ad-4791-ad18-d75be67f75ad

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_treeExp_lt_iff_isInaccessible_of_isRegular

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (hreg : κ.IsRegular) :
    (∀ lam μ : Cardinal.{w}, ℵ₀ ≤ μ → μ ≤ lam → lam < κ → treeExp lam μ < κ) ↔
      κ.IsInaccessible := by
  exact treeExp_lt_iff_isInaccessible_of_isRegular κ hunc hreg
end JardenShami
