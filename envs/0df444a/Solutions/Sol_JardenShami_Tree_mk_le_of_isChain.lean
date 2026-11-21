-- Prove2me | solution 1 for JardenShami.Tree.mk_le_of_isChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:57.960171+00:00
-- url     : https://prove2.me/submissions/a401c013-010e-4011-b5cc-a1a5b331146a

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Kappa_mk_eq
import Theorems.Thm_JardenShami_Tree_ht_injOn_of_isChain
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
import Theorems.Thm_JardenShami_Tree_ht_lt_height
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami.Tree
theorem _root_.solution {κ : Cardinal.{w}} (hT : height T = κ.ord) {b : Set T}
    (hb : IsChain (· ≤ ·) b) : #b ≤ κ := by
  have hlt : ∀ x : b, ht (x : T) < κ.ord := fun x => hT ▸ ht_lt_height (x : T)
  rw [← Kappa.mk_eq κ]
  refine Cardinal.mk_le_of_injective (f := fun x : b => Kappa.mk (ht (x : T)) (hlt x)) ?_
  intro x y h
  have := congrArg (fun z : Kappa κ => (z : Ordinal.{w})) h
  simp only [Kappa.coe_mk] at this
  exact Subtype.ext (ht_injOn_of_isChain hb x.2 y.2 this)
end JardenShami.Tree
