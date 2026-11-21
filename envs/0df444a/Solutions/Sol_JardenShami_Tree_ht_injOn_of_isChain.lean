-- Prove2me | solution 1 for JardenShami.Tree.ht_injOn_of_isChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:46.384959+00:00
-- url     : https://prove2.me/submissions/b5b6a435-41cf-4000-ade0-16d2510b7dee

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Tree_eq_of_le_of_le_of_ht_eq


set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami.Tree
theorem _root_.solution {b : Set T} (hb : IsChain (· ≤ ·) b) : Set.InjOn ht b := by
  intro x hx y hy h
  rcases hb.total hx hy with h' | h'
  · exact eq_of_le_of_le_of_ht_eq h' le_rfl h
  · exact (eq_of_le_of_le_of_ht_eq h' le_rfl h.symm).symm
end JardenShami.Tree
