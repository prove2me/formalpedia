-- Prove2me | solution 1 for JardenShami.height_binTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:59.579542+00:00
-- url     : https://prove2.me/submissions/ab81d36f-6b26-4906-998a-dda7507456a5

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_ht_binRestr
import Theorems.Thm_JardenShami_Kappa_coe_mk
attribute [local simp] JardenShami.Kappa.coe_mk



set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {ν : Cardinal.{w}}
namespace JardenShami
theorem _root_.solution : height (binTree ν) = ν.ord := by
  refine IsLeast.csInf_eq ⟨?_, fun α hα => ?_⟩
  · refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    obtain ⟨_, f, β, rfl⟩ := g
    have h : ht (⟨binRestr f β, f, β, rfl⟩ : binTree ν) = ν.ord := hg
    rw [ht_binRestr] at h
    exact (Kappa.coe_lt_ord β).ne h
  · by_contra hc
    have hlt := lt_of_not_ge hc
    let b : Kappa ν := Kappa.mk α hlt
    have hmem : (⟨binRestr (fun _ => 0) b, _, b, rfl⟩ : binTree ν) ∈ Lev (binTree ν) α := by
      change ht _ = α
      rw [ht_binRestr, Kappa.coe_mk]
    have hα' : Lev (binTree ν) α = ∅ := hα
    rw [hα'] at hmem
    exact hmem
end JardenShami
