-- Prove2me | solution 1 for JardenShami.height_treeOfColoring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:12.13331+00:00
-- url     : https://prove2.me/submissions/a3916a08-8c8e-4b9b-883a-045b9ff548d8

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_mem_lev_treeOfColoring
import Theorems.Thm_JardenShami_Kappa_coe_mk
attribute [local simp] JardenShami.Kappa.coe_mk



set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type w}
namespace JardenShami
theorem _root_.solution (C : Coloring (Kappa κ) D) :
    height (treeOfColoring C) = κ.ord := by
  refine IsLeast.csInf_eq ⟨?_, fun α hα => ?_⟩
  · refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    obtain ⟨δ, β, h, -, hβ⟩ := mem_lev_treeOfColoring.1 hg
    exact (Kappa.coe_lt_ord β).ne hβ
  · by_contra hc
    have hlt := lt_of_not_ge hc
    let b : Kappa κ := Kappa.mk α hlt
    have hmem : (⟨fiberRestr C b b le_rfl, b, b, le_rfl, rfl⟩ : treeOfColoring C) ∈
        Lev (treeOfColoring C) α :=
      mem_lev_treeOfColoring.2 ⟨b, b, le_rfl, rfl, Kappa.coe_mk _ _⟩
    have hα' : Lev (treeOfColoring C) α = ∅ := hα
    rw [hα'] at hmem
    exact hmem
end JardenShami
