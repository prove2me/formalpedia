-- Prove2me | solution 1 for JardenShami.treeExp_le_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:55.550862+00:00
-- url     : https://prove2.me/submissions/9d2d22c6-da7e-4134-b09b-35b1e0359c5d

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_treeExp_le_add_one_power

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (lam μ : Cardinal.{w}) (hlam : ℵ₀ ≤ lam) :
    treeExp lam μ ≤ lam ^ μ := by
  calc treeExp lam μ ≤ (lam + 1) ^ μ := treeExp_le_add_one_power lam μ
    _ = lam ^ μ := by rw [Cardinal.add_one_of_aleph0_le hlam]
end JardenShami
