-- Prove2me | solution 1 for JardenShami.nonempty_iso_treeOfColoring_historyTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:39.975984+00:00
-- url     : https://prove2.me/submissions/2f18a25b-f69a-46ea-9d3f-7daf900064ba

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
import Theorems.Thm_JardenShami_fiberRestr_subset_iff_histFun_subset
import Theorems.Thm_JardenShami_fiberRestr_eq_iff_histFun_eq
import Theorems.Thm_JardenShami_exists_histFun_node_eq
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (hT : IsKappaTree κ T) (e : Enumeration κ T)
    (he : e.Covers) {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C) :
    Nonempty (treeOfColoring C ≃o HistoryTree T) := by
  classical
  let δ : treeOfColoring C → Kappa κ := fun g => g.2.choose
  let β : treeOfColoring C → Kappa κ := fun g => Classical.choose (Classical.choose_spec g.2)
  have hβ : ∀ g : treeOfColoring C, ∃ h, g.1 = fiberRestr C (δ g) (β g) h :=
    fun g => Classical.choose_spec (Classical.choose_spec g.2)
  let hβδ : ∀ g, β g ≤ δ g := fun g => (hβ g).choose
  have hg : ∀ g : treeOfColoring C, g.1 = fiberRestr C (δ g) (β g) (hβδ g) :=
    fun g => (hβ g).choose_spec
  let Φ : treeOfColoring C → HistoryTree T :=
    fun g => ⟨histFun (e.node C (β g) (δ g) (hβδ g)), _, rfl⟩
  have hΦ : ∀ a b, Φ a ≤ Φ b ↔ a ≤ b := by
    intro a b
    change histFun _ ⊆ histFun _ ↔ a.1 ⊆ b.1
    rw [hg a, hg b, fiberRestr_subset_iff_histFun_subset hT e hC]
  refine ⟨RelIso.ofSurjective (OrderEmbedding.ofMapLEIff Φ hΦ) ?_⟩
  rintro ⟨_, t, rfl⟩
  obtain ⟨β₀, δ₀, h₀, hh⟩ := exists_histFun_node_eq hT e he hC t
  let g : treeOfColoring C := ⟨fiberRestr C δ₀ β₀ h₀, δ₀, β₀, h₀, rfl⟩
  refine ⟨g, Subtype.ext ?_⟩
  change histFun (e.node C (β g) (δ g) (hβδ g)) = histFun t
  rw [← hh, ← fiberRestr_eq_iff_histFun_eq hT e hC]
  exact (hg g).symm
end JardenShami
