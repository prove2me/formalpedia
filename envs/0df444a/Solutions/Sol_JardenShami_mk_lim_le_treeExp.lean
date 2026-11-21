-- Prove2me | solution 1 for JardenShami.mk_lim_le_treeExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:22.094716+00:00
-- url     : https://prove2.me/submissions/b2304eea-157e-4d06-8020-0493aa590ddb

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
theorem _root_.solution {T : Type w} [PartialOrder T] [IsTree T] {lam μ : Cardinal.{w}}
    (hT : height T = μ.ord) (hcard : #T ≤ lam) : #(Lim T) ≤ treeExp lam μ := by
  refine le_csSup ⟨(lam + 1) ^ μ, ?_⟩ ⟨T, inferInstance, inferInstance, hT, hcard, rfl⟩
  rintro c ⟨T', _, _, hT', hcard', rfl⟩
  exact (mk_lim_le hT').trans (Cardinal.power_le_power_right (by gcongr))
end JardenShami
