-- Prove2me | solution 1 for JardenShami.treeExp_le_add_one_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:17.806231+00:00
-- url     : https://prove2.me/submissions/31ccda67-639b-4569-aec1-e1b8bcf9440f

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_mk_lim_le

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (lam μ : Cardinal.{w}) : treeExp lam μ ≤ (lam + 1) ^ μ := by
  refine csSup_le' ?_
  rintro c ⟨T, _, _, hT, hcard, rfl⟩
  exact (mk_lim_le hT).trans (Cardinal.power_le_power_right (by gcongr))
end JardenShami
