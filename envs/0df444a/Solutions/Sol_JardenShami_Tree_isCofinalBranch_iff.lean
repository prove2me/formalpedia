-- Prove2me | solution 1 for JardenShami.Tree.isCofinalBranch_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:05.711903+00:00
-- url     : https://prove2.me/submissions/37935448-4943-4b3a-8d35-0074c5b81062

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Tree_lt_iff_ht_lt_of_isChain
import Theorems.Thm_JardenShami_Tree_ht_injOn_of_isChain
import Theorems.Thm_JardenShami_Tree_isWellOrder_of_isChain
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
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
theorem _root_.solution {κ : Cardinal.{w}} (hT : height T = κ.ord) {b : Set T} :
    IsCofinalBranch b ↔ IsBranch b ∧ #b = κ := by
  constructor
  · rintro ⟨hb, h, htype⟩
    refine ⟨hb, ?_⟩
    rw [← @Ordinal.card_type _ _ h, htype, hT, Cardinal.card_ord]
  · rintro ⟨hb, hcard⟩
    have := isWellOrder_of_isChain hb.1
    refine ⟨hb, inferInstance, le_antisymm ?_ ?_⟩
    · have hlt : ∀ x : b, ht (x : T) < κ.ord := fun x => hT ▸ ht_lt_height (x : T)
      rw [hT, ← Ordinal.type_toType κ.ord]
      refine Ordinal.type_le_iff'.2 ⟨⟨⟨fun x => Kappa.mk (ht (x : T)) (hlt x), ?_⟩, ?_⟩⟩
      · intro x y h
        have := congrArg (fun z : Kappa κ => (z : Ordinal.{w})) h
        simp only [Kappa.coe_mk] at this
        exact Subtype.ext (ht_injOn_of_isChain hb.1 x.2 y.2 this)
      · intro x y
        change Kappa.mk (ht (x : T)) (hlt x) < Kappa.mk (ht (y : T)) (hlt y) ↔ (x : T) < y
        rw [← Kappa.coe_lt_coe, Kappa.coe_mk, Kappa.coe_mk,
          ← lt_iff_ht_lt_of_isChain hb.1 x.2 y.2]
    · rw [hT, Cardinal.ord_le, Ordinal.card_type, hcard]
end JardenShami.Tree
