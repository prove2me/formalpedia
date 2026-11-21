-- Prove2me | solution 1 for JardenShami.treeExp_lt_iff_isInaccessible_of_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:05.135679+00:00
-- url     : https://prove2.me/submissions/e93abf8b-ef66-4c96-a6df-5c2568c1a18f

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_treeExp_le_power
import Theorems.Thm_JardenShami_power_lt_of_isInaccessible
import Theorems.Thm_JardenShami_two_power_lt_of_treeExp_lt

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
  constructor
  · intro h
    refine Cardinal.isInaccessible_def.2 ⟨hunc, hreg, ⟨(Cardinal.aleph0_pos.trans hunc).ne', ?_⟩⟩
    exact fun ν hν => two_power_lt_of_treeExp_lt hreg h ν hν
  · intro hκ lam μ hμ hμlam hlam
    exact (treeExp_le_power lam μ (hμ.trans hμlam)).trans_lt
      (power_lt_of_isInaccessible hκ hlam (hμlam.trans_lt hlam))
end JardenShami
